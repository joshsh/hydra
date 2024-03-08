module Hydra.Langs.Haskell.Coder (moduleToHaskell) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Langs.Haskell.Language
import Hydra.Langs.Haskell.Utils
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
import Hydra.Langs.Haskell.Serde
import Hydra.Langs.Haskell.Settings
import Hydra.Lib.Io
import qualified Hydra.Langs.Haskell.Ast as H
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Dsl.Types as Types

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import Hydra.Rewriting (removeTypeAnnotations, removeTermAnnotations)


adaptTypeToHaskellAndEncode :: Namespaces -> Type -> Flow Graph H.Type
adaptTypeToHaskellAndEncode namespaces = adaptAndEncodeType haskellLanguage (encodeType namespaces)

constantDecls :: Graph -> Namespaces -> Name -> Type -> [H.DeclarationWithComments]
constantDecls g namespaces name@(Name nm) typ = if useCoreImport
    then toDecl (Name "hydra/core.Name") nameDecl:(toDecl (Name "hydra/core.FieldName") <$> fieldDecls)
    else []
  where
    lname = localNameOfEager name
    toDecl n (k, v) = H.DeclarationWithComments decl Nothing
      where
        decl = H.DeclarationValueBinding $ H.ValueBindingSimple $ H.ValueBinding_Simple pat rhs Nothing
        pat = applicationPattern (simpleName k) []
        rhs = H.RightHandSide $ H.ExpressionApplication $ H.Expression_Application
          (H.ExpressionVariable $ elementReference namespaces n)
          (H.ExpressionLiteral $ H.LiteralString v)
    nameDecl = ("_" ++ lname, nm)
    fieldsOf t = case stripType t of
      TypeRecord rt -> rowTypeFields rt
      TypeUnion rt -> rowTypeFields rt
      _ -> []
    fieldDecls = toConstant <$> fieldsOf (snd $ unpackLambdaType g typ)
    toConstant (FieldType (FieldName fname) _) = ("_" ++ lname ++ "_" ++ fname, fname)

constructModule :: Namespaces
  -> Module
  -> M.Map Type (Coder Graph Graph Term H.Expression)
  -> [Element] -> Flow Graph H.Module
constructModule namespaces mod coders els = do
    pairs <- CM.mapM toLegacyPair els
    g <- getState
    decls <- L.concat <$> CM.mapM (createDeclarations g) pairs
    let mc = moduleDescription mod
    return $ H.Module (Just $ H.ModuleHead mc (importName $ h $ moduleNamespace mod) []) imports decls
  where
    toLegacyPair el = do
      let term = elementData el
      typ <- requireTermType term
      return (el, TypedTerm typ term)
    h (Namespace name) = name

    createDeclarations g pair@(el, TypedTerm typ term) = if isType typ
      then toTypeDeclarations namespaces el term
      else fail $ "name: " ++ unName (elementName el)
--      else do
--        d <- toDataDeclaration coders namespaces pair
--        return [d]

    importName name = H.ModuleName $ L.intercalate "." (capitalize <$> Strings.splitOn "/" name)
    imports = domainImports ++ standardImports
      where
        domainImports = toImport <$> M.toList (namespacesMapping namespaces)
          where
            toImport (Namespace name, alias) = H.Import True (importName name) (Just alias) Nothing
        standardImports = toImport <$> [
            ("Data.Int", Nothing),
            ("Data.List", Just "L"),
            ("Data.Map", Just "M"),
            ("Data.Set", Just "S")]
          where
            toImport (name, alias) = H.Import False (H.ModuleName name) (H.ModuleName <$> alias) Nothing

encodeFunction :: Namespaces -> Function -> Flow Graph H.Expression
encodeFunction namespaces fun = case fun of
    FunctionElimination e -> case e of
      EliminationList fun -> do
        let lhs = hsvar "L.foldl"
        rhs <- encodeTerm namespaces fun
        return $ hsapp lhs rhs
      EliminationWrap name -> pure $ H.ExpressionVariable $ elementReference namespaces $
        qname (Y.fromJust $ namespaceOfEager name) $ newtypeAccessorName name
      EliminationOptional (OptionalCases nothing just) -> do
        nothingRhs <- H.CaseRhs <$> encodeTerm namespaces nothing
        let nothingAlt = H.Alternative (H.PatternName $ rawName "Nothing") nothingRhs Nothing
        justAlt <- do
          -- Note: some of the following could be brought together with FunctionCases
          let v0 = "v"
          let rhsTerm = simplifyTerm $ apply just (var v0)
          let v1 = if S.member (Name v0) $ freeVariablesInTerm rhsTerm then v0 else ignoredVariable
          let lhs = applicationPattern (rawName "Just") [H.PatternName $ rawName v1]
          rhs <- H.CaseRhs <$> encodeTerm namespaces rhsTerm
          return $ H.Alternative lhs rhs Nothing
        return $ hslambda "x" $ H.ExpressionCase $ H.Expression_Case (hsvar "x") [nothingAlt, justAlt]
      EliminationProduct (TupleProjection arity idx) -> if arity == 2
        then return $ hsvar $ if idx == 0 then "fst" else "snd"
        else fail "Eliminations for tuples of arity > 2 are not supported yet in the Haskell coder"
      EliminationRecord (Projection dn fname) -> return $ H.ExpressionVariable $ recordFieldReference namespaces dn fname
      EliminationUnion (CaseStatement dn def fields) -> hslambda "x" <$> caseExpr -- note: could use a lambda case here
        where
          caseExpr = do
            t <- withSchemaContext $ requireType dn
            rt <- toUnionType dn t
            let fieldMap = M.fromList $ (\f -> (fieldTypeName f, f)) <$> rowTypeFields rt
            ecases <- CM.mapM (toAlt fieldMap) fields
            dcases <- case def of
              Nothing -> pure []
              Just d -> do
                cs <- H.CaseRhs <$> encodeTerm namespaces d
                let lhs = H.PatternName $ rawName ignoredVariable
                return [H.Alternative lhs cs Nothing]
            return $ H.ExpressionCase $ H.Expression_Case (hsvar "x") $ ecases ++ dcases
          toAlt fieldMap (Field fn fun') = do
            let v0 = "v"
            let raw = apply fun' (var v0)
            let rhsTerm = simplifyTerm raw
            let v1 = if isFreeIn (Name v0) rhsTerm then ignoredVariable else v0
            let hname = unionFieldReference namespaces dn fn
            args <- case M.lookup fn fieldMap of
              Just (FieldType _ ft) -> case stripType ft of
                TypeRecord (RowType _ Nothing []) -> pure []
                _ -> pure [H.PatternName $ rawName v1]
              Nothing -> fail $ "field " ++ show fn ++ " not found in " ++ show dn
            let lhs = applicationPattern hname args
            rhs <- H.CaseRhs <$> encodeTerm namespaces rhsTerm
            return $ H.Alternative lhs rhs Nothing
    FunctionLambda (Lambda (Name v) _ body) -> hslambda v <$> encodeTerm namespaces body
    FunctionPrimitive name -> pure $ H.ExpressionVariable $ hsPrimitiveReference name

encodeLiteral :: Literal -> Flow Graph H.Expression
encodeLiteral av = case av of
    LiteralBoolean b -> pure $ hsvar $ if b then "True" else "False"
    LiteralFloat fv -> case fv of
      FloatValueFloat32 f -> pure $ hslit $ H.LiteralFloat f
      FloatValueFloat64 f -> pure $ hslit $ H.LiteralDouble f
      _ -> unexpected "floating-point number" $ show fv
    LiteralInteger iv -> case iv of
      IntegerValueBigint i -> pure $ hslit $ H.LiteralInteger i
      IntegerValueInt32 i -> pure $ hslit $ H.LiteralInt i
      _ -> unexpected "integer" $ show iv
    LiteralString s -> pure $ hslit $ H.LiteralString s
    _ -> unexpected "literal value" $ show av

encodeTerm :: Namespaces -> Term -> Flow Graph H.Expression
encodeTerm namespaces term = do
   case stripTerm term of
    TermApplication (Application fun arg) -> hsapp <$> encode fun <*> encode arg
    TermFunction f -> encodeFunction namespaces f
    TermLet (Let bindings env) -> do
        hbindings <- CM.mapM encodeBinding bindings
        hinner <- encode env
        return $ H.ExpressionLet $ H.Expression_Let hbindings hinner
      where
        encodeBinding (Field (FieldName name) term) = do
          let hname = simpleName name
          hexpr <- encode term
          return $ H.LocalBindingValue $ simpleValueBinding hname hexpr Nothing
    TermList els -> H.ExpressionList <$> CM.mapM encode els
    TermLiteral v -> encodeLiteral v
    TermWrap (Nominal tname term') -> if newtypesNotTypedefs
      then hsapp <$> pure (H.ExpressionVariable $ elementReference namespaces tname) <*> encode term'
      else encode term'
    TermOptional m -> case m of
      Nothing -> pure $ hsvar "Nothing"
      Just t -> hsapp (hsvar "Just") <$> encode t
    TermProduct terms -> H.ExpressionTuple <$> (CM.mapM encode terms)
    TermRecord (Record sname fields) -> do
      if L.null fields -- TODO: too permissive; not all empty record types are the unit type
        then pure $ H.ExpressionTuple []
        else do
            let typeName = elementReference namespaces sname
            updates <- CM.mapM toFieldUpdate fields
            return $ H.ExpressionConstructRecord $ H.Expression_ConstructRecord typeName updates
          where
            toFieldUpdate (Field fn ft) = H.FieldUpdate (recordFieldReference namespaces sname fn) <$> encode ft
    TermUnion (Injection sname (Field fn ft)) -> do
      let lhs = H.ExpressionVariable $ unionFieldReference namespaces sname fn
      case stripTerm ft of
        TermRecord (Record _ []) -> pure lhs
        _ -> hsapp lhs <$> encode ft
    TermVariable name -> pure $ H.ExpressionVariable $ elementReference namespaces name --pure $ hsvar v
    _ -> fail $ "unexpected term: " ++ show term
  where
    encode = encodeTerm namespaces

encodeType :: Namespaces -> Type -> Flow Graph H.Type
encodeType namespaces typ = withTrace "encode type" $ case stripType typ of
    TypeApplication (ApplicationType lhs rhs) -> toTypeApplication <$> CM.sequence [encode lhs, encode rhs]
    TypeFunction (FunctionType dom cod) -> H.TypeFunction <$> (H.Type_Function <$> encode dom <*> encode cod)
    TypeLambda (LambdaType _ body) -> encode body
    TypeList lt -> H.TypeList <$> encode lt
    TypeLiteral lt -> H.TypeVariable . rawName <$> case lt of
      LiteralTypeBoolean -> pure "Bool"
      LiteralTypeFloat ft -> case ft of
        FloatTypeFloat32 -> pure "Float"
        FloatTypeFloat64 -> pure "Double"
        _ -> fail $ "unexpected floating-point type: " ++ show ft
      LiteralTypeInteger it -> case it of
        IntegerTypeBigint -> pure "Integer"
        IntegerTypeInt8 -> pure "Int8"
        IntegerTypeInt16 -> pure "Int16"
        IntegerTypeInt32 -> pure "Int"
        IntegerTypeInt64 -> pure "Int64"
        _ -> fail $ "unexpected integer type: " ++ show it
      LiteralTypeString -> pure "String"
      _ -> fail $ "unexpected literal type: " ++ show lt
    TypeMap (MapType kt vt) -> toTypeApplication <$> CM.sequence [
      pure $ H.TypeVariable $ rawName "Map",
      encode kt,
      encode vt]
    TypeOptional ot -> toTypeApplication <$> CM.sequence [
      pure $ H.TypeVariable $ rawName "Maybe",
      encode ot]
    TypeProduct types -> H.TypeTuple <$> (CM.mapM encode types)
    TypeRecord rt -> case rowTypeFields rt of
      [] -> pure $ H.TypeTuple []  -- TODO: too permissive; not all empty record types are the unit type
      _ -> wrap $ rowTypeTypeName rt
    TypeSet st -> toTypeApplication <$> CM.sequence [
      pure $ H.TypeVariable $ rawName "Set",
      encode st]
    TypeUnion rt -> wrap $ rowTypeTypeName rt
    TypeVariable v -> wrap v
    TypeWrap (Nominal name _) -> wrap name
    _ -> fail $ "unexpected type: " ++ show typ
  where
    encode = encodeType namespaces
    wrap name = pure $ H.TypeVariable $ elementReference namespaces name

encodeTypeWithClassAssertions :: Namespaces -> M.Map Name (S.Set TypeClass) -> Type -> Flow Graph H.Type
encodeTypeWithClassAssertions namespaces classes typ = withTrace "encode with assertions" $ do
  htyp <- adaptTypeToHaskellAndEncode namespaces typ
  if L.null assertPairs
    then pure htyp
    else do
      let encoded = encodeAssertion <$> assertPairs
      let hassert = if L.length encoded > 1 then L.head encoded else H.AssertionTuple encoded
      return $ H.TypeCtx $ H.Type_Context hassert htyp
  where
    encodeAssertion (name, cls) = H.AssertionClass $ H.Assertion_Class hname [htype]
      where
        hname = rawName $ case cls of
          TypeClassEquality -> "Eq"
          TypeClassOrdering -> "Ord"
        htype = H.TypeVariable $ rawName $ unName name -- TODO: sanitization

    assertPairs = L.concat (toPairs <$> M.toList classes)
      where
        toPairs (name, cls) = toPair <$> S.toList cls
          where
            toPair c = (name, c)

moduleToHaskellModule :: Module -> Flow Graph H.Module
moduleToHaskellModule mod = do
    namespaces <- namespacesForModule mod
    transformModule haskellLanguage (encodeTerm namespaces) (constructModule namespaces) mod

moduleToHaskell :: Module -> Flow Graph (M.Map FilePath String)
moduleToHaskell mod = do
  hsmod <- moduleToHaskellModule mod
  let s = printExpr $ parenthesize $ toTree hsmod
  return $ M.fromList [(namespaceToFilePath True (FileExtension "hs") $ moduleNamespace mod, s)]

toDataDeclaration :: M.Map Type (Coder Graph Graph Term H.Expression) -> Namespaces
  -> (Element, TypedTerm) -> Flow Graph H.DeclarationWithComments
toDataDeclaration coders namespaces (el, TypedTerm typ term) = toDecl hname term coder Nothing
  where
    coder = Y.fromJust $ M.lookup typ coders
    hname = simpleName $ localNameOfEager $ elementName el

    rewriteValueBinding vb = case vb of
      H.ValueBindingSimple (H.ValueBinding_Simple (H.PatternApplication (H.Pattern_Application name args)) rhs bindings) -> case rhs of
        H.RightHandSide (H.ExpressionLambda (H.Expression_Lambda vars body)) -> rewriteValueBinding $
          H.ValueBindingSimple $ H.ValueBinding_Simple
            (applicationPattern name (args ++ vars)) (H.RightHandSide body) bindings
        _ -> vb

    toDecl hname term coder bindings = case stripTerm term of
      TermLet (Let lbindings env) -> do
          -- A "let" constant cannot be predicted in advance, so we infer its type and construct a coder on the fly
          -- This makes program code with "let" terms more expensive to transform than simple data.
          let bl = lbindings
          ts <- (CM.mapM inferredTypeOf (fieldTerm <$> bl))
          coders <- CM.mapM (constructCoder haskellLanguage (encodeTerm namespaces)) ts
          let hnames = simpleName <$> (unFieldName . fieldName <$> bl)
          hterms <- CM.zipWithM coderEncode coders (fieldTerm <$> bl)

          let hbindings = L.zipWith toBinding hnames hterms
          toDecl hname env coder (Just $ H.LocalBindings hbindings)
        where
          toBinding hname' hterm' = H.LocalBindingValue $ simpleValueBinding hname' hterm' Nothing
      _ -> do
        hterm <- coderEncode coder term
        let vb = simpleValueBinding hname hterm bindings
        classes <- annotationClassTypeClasses kvAnnotationClass typ
        htype <- encodeTypeWithClassAssertions namespaces classes typ
        let decl = H.DeclarationTypedBinding $ H.TypedBinding (H.TypeSignature hname htype) (rewriteValueBinding vb)
        comments <- annotationClassTermDescription kvAnnotationClass term
        return $ H.DeclarationWithComments decl comments

toTypeDeclarations :: Namespaces -> Element -> Term -> Flow Graph [H.DeclarationWithComments]
toTypeDeclarations namespaces el term = withTrace ("type element " ++ unName (elementName el)) $ do
    let lname = localNameOfEager $ elementName el
    let hname = simpleName lname
    t <- coreDecodeType term
    isSer <- isSerializable el
    let deriv = H.Deriving $ if isSer
                  then rawName <$> ["Eq", "Ord", "Read", "Show"]
                  else []
    g <- getState
    let (vars, t') = unpackLambdaType g t
    let hd = declHead hname $ L.reverse vars
    decl <- case stripType t' of
      TypeRecord rt -> do
        cons <- recordCons lname $ rowTypeFields rt
        return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordData [] hd [cons] [deriv]
      TypeUnion rt -> do
        cons <- CM.mapM (unionCons lname) $ rowTypeFields rt
        return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordData [] hd cons [deriv]
      TypeWrap (Nominal tname wt) -> do
        cons <- newtypeCons el wt
        return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordNewtype [] hd [cons] [deriv]
      _ -> if newtypesNotTypedefs
        then do
          cons <- newtypeCons el t'
          return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordNewtype [] hd [cons] [deriv]
        else do
          htype <- adaptTypeToHaskellAndEncode namespaces t
          return $ H.DeclarationType (H.TypeDeclaration hd htype)
    comments <- annotationClassTermDescription kvAnnotationClass term
    return $ [H.DeclarationWithComments decl comments] ++ constantDecls g namespaces (elementName el) t
  where
    declHead name vars = case vars of
      [] -> H.DeclarationHeadSimple name
      ((Name h):rest) -> H.DeclarationHeadApplication $
        H.DeclarationHead_Application (declHead name rest) (H.Variable $ simpleName h)

    newtypeCons el typ = do
        let hname = simpleName $ newtypeAccessorName $ elementName el
        htype <- adaptTypeToHaskellAndEncode namespaces typ
        comments <- annotationClassTypeDescription kvAnnotationClass typ
        let hfield = H.FieldWithComments (H.Field hname htype) comments
        return $ H.ConstructorWithComments
          (H.ConstructorRecord $ H.Constructor_Record (simpleName $ localNameOfEager $ elementName el) [hfield]) Nothing

    recordCons lname fields = do
        hFields <- CM.mapM toField fields
        return $ H.ConstructorWithComments (H.ConstructorRecord $ H.Constructor_Record (simpleName lname) hFields) Nothing
      where
        toField (FieldType (FieldName fname) ftype) = do
          let hname = simpleName $ decapitalize lname ++ capitalize fname
          htype <- adaptTypeToHaskellAndEncode namespaces ftype
          comments <- annotationClassTypeDescription kvAnnotationClass ftype
          return $ H.FieldWithComments (H.Field hname htype) comments

    unionCons lname (FieldType (FieldName fname) ftype) = do
      comments <- annotationClassTypeDescription kvAnnotationClass ftype
      let nm = capitalize lname ++ capitalize fname
      typeList <- if stripType ftype == Types.unit
        then pure []
        else do
          htype <- adaptTypeToHaskellAndEncode namespaces ftype
          return [htype]
      return $ H.ConstructorWithComments (H.ConstructorOrdinary $ H.Constructor_Ordinary (simpleName nm) typeList) comments
