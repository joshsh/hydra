module Hydra.Ext.Haskell.Coder (moduleToHaskell) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Ext.Haskell.Language
import Hydra.Ext.Haskell.Utils
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
import Hydra.Ext.Haskell.Serde
import Hydra.Ext.Haskell.Settings
import qualified Hydra.Ext.Haskell.Ast as H
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.ShorthandTypes
import Hydra.Lib.Io
import qualified Hydra.Decode as Decode

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import Hydra.Rewriting (removeTypeAnnotations, removeTermAnnotations)


data HaskellGenerationOptions = HaskellGenerationOptions {
  haskellGenerationOptionsIncludeTypeDefinitions :: Bool
}

key_haskellVar = Name "haskellVar"

-- TODO: make these settings configurable
defaultHaskellGenerationOptions = HaskellGenerationOptions False

adaptTypeToHaskellAndEncode :: HaskellNamespaces -> Type -> Flow Graph H.Type
adaptTypeToHaskellAndEncode namespaces = adaptAndEncodeType haskellLanguage (encodeType namespaces)

constantForFieldName tname fname = "_" ++ localNameOfEager tname ++ "_" ++ unName fname
constantForTypeName tname = "_" ++ localNameOfEager tname

constructModule :: HaskellNamespaces
  -> Module
  -> M.Map Type (Coder Graph Graph Term H.Expression)
  -> [(Element, TypedTerm)] -> Flow Graph H.Module
constructModule namespaces mod coders pairs = do
    g <- getState
    decls <- L.concat <$> CM.mapM (createDeclarations g) pairs
    let mc = moduleDescription mod
    return $ H.Module (Just $ H.ModuleHead mc (importName $ h $ moduleNamespace mod) []) imports decls
  where
    h (Namespace name) = name

    createDeclarations g pair@(el, TypedTerm term typ) = do
      if isType typ
        then toTypeDeclarations namespaces el term
        else do
          d <- toDataDeclaration coders namespaces pair
          return [d]

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

encodeFunction :: HaskellNamespaces -> Function -> Flow Graph H.Expression
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
          v0 <- (\i -> "v" ++ show i) <$> nextCount key_haskellVar
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
            rt <- withSchemaContext $ requireUnionType dn
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
            v0 <- (\i -> "v" ++ show i) <$> nextCount key_haskellVar
            let raw = apply fun' (var v0)
            let rhsTerm = simplifyTerm raw
            let v1 = if isFreeIn (Name v0) rhsTerm then ignoredVariable else v0
            let hname = unionFieldReference namespaces dn fn
            args <- case M.lookup fn fieldMap of
              Just (FieldType _ ft) -> case stripType ft of
                TypeRecord (RowType _ []) -> pure []
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

encodeTerm :: HaskellNamespaces -> Term -> Flow Graph H.Expression
encodeTerm namespaces term = do
   case fullyStripTerm term of
    TermApplication (Application fun arg) -> hsapp <$> encode fun <*> encode arg
    TermFunction f -> encodeFunction namespaces f
    TermLet (Let bindings env) -> do
        hbindings <- CM.mapM encodeBinding bindings
        hinner <- encode env
        return $ H.ExpressionLet $ H.Expression_Let hbindings hinner
      where
        encodeBinding (LetBinding name term _) = do
          let hname = simpleName $ unName name
          hexpr <- encode term
          return $ H.LocalBindingValue $ simpleValueBinding hname hexpr Nothing
    TermList els -> H.ExpressionList <$> CM.mapM encode els
    TermLiteral v -> encodeLiteral v
    TermWrap (WrappedTerm tname term') -> if newtypesNotTypedefs
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
      case fullyStripTerm ft of
        TermRecord (Record _ []) -> pure lhs
        _ -> hsapp lhs <$> encode ft
    TermVariable name -> pure $ H.ExpressionVariable $ elementReference namespaces name --pure $ hsvar v
    t -> fail $ "unexpected term: " ++ show t
  where
    encode = encodeTerm namespaces

encodeType :: HaskellNamespaces -> Type -> Flow Graph H.Type
encodeType namespaces typ = withTrace "encode type" $ case stripType typ of
    TypeApplication (ApplicationType lhs rhs) -> toTypeApplication <$> CM.sequence [encode lhs, encode rhs]
    TypeFunction (FunctionType dom cod) -> H.TypeFunction <$> (H.Type_Function <$> encode dom <*> encode cod)
    TypeLambda (LambdaType (Name v) body) -> toTypeApplication <$> CM.sequence [
      encode body,
      pure $ H.TypeVariable $ simpleName v]
    TypeList lt -> H.TypeList <$> encode lt
    TypeLiteral lt -> H.TypeVariable . rawName <$> case lt of
      LiteralTypeBoolean -> pure "Bool"
      LiteralTypeFloat ft -> case ft of
        FloatTypeFloat32 -> pure "Float"
        FloatTypeFloat64 -> pure "Double"
        FloatTypeBigfloat -> pure "Double" -- TODO: type adapter should prevent this
--        _ -> fail $ "unexpected floating-point type: " ++ show ft
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
      _ -> ref $ rowTypeTypeName rt
    TypeSet st -> toTypeApplication <$> CM.sequence [
      pure $ H.TypeVariable $ rawName "Set",
      encode st]
    TypeUnion rt -> ref $ rowTypeTypeName rt
    TypeVariable v -> ref v
    TypeWrap (WrappedType name _) -> ref name
    _ -> fail $ "unexpected type: " ++ show typ
  where
    encode = encodeType namespaces
    ref name = pure $ H.TypeVariable $ elementReference namespaces name

encodeTypeWithClassAssertions :: HaskellNamespaces -> M.Map Name (S.Set TypeClass) -> Type -> Flow Graph H.Type
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

nameDecls :: Graph -> HaskellNamespaces -> Name -> Type -> [H.DeclarationWithComments]
nameDecls g namespaces name@(Name nm) typ = if useCoreImport
    then (toDecl _Name nameDecl):(toDecl _Name <$> fieldDecls)
    else []
  where
    toDecl n (k, v) = H.DeclarationWithComments decl Nothing
      where
        decl = H.DeclarationValueBinding $ H.ValueBindingSimple $ H.ValueBinding_Simple pat rhs Nothing
        pat = applicationPattern (simpleName k) []
        rhs = H.RightHandSide $ H.ExpressionApplication $ H.Expression_Application
          (H.ExpressionVariable $ elementReference namespaces n)
          (H.ExpressionLiteral $ H.LiteralString v)
    nameDecl = (constantForTypeName name, nm)
    fieldDecls = toConstant <$> fieldsOf typ
    toConstant (FieldType fname _) = (constantForFieldName name fname, unName fname)

toDataDeclaration :: M.Map Type (Coder Graph Graph Term H.Expression) -> HaskellNamespaces
  -> (Element, TypedTerm) -> Flow Graph H.DeclarationWithComments
toDataDeclaration coders namespaces (el, TypedTerm term typ) = do
  comments <- getTermDescription term
  toDecl comments hname term coder Nothing
  where
    coder = Y.fromJust $ M.lookup typ coders
    hname = simpleName $ localNameOfEager $ elementName el

    rewriteValueBinding vb = case vb of
      H.ValueBindingSimple (H.ValueBinding_Simple (H.PatternApplication (H.Pattern_Application name args)) rhs bindings) -> case rhs of
        H.RightHandSide (H.ExpressionLambda (H.Expression_Lambda vars body)) -> rewriteValueBinding $
          H.ValueBindingSimple $ H.ValueBinding_Simple
            (applicationPattern name (args ++ vars)) (H.RightHandSide body) bindings
        _ -> vb

    toDecl comments hname term coder bindings = case fullyStripTerm term of
      TermLet (Let lbindings env) -> do
          -- A "let" constant cannot be predicted in advance, so we infer its type and construct a coder on the fly
          -- This makes program code with "let" terms more expensive to transform than simple data.
          ts <- (CM.mapM inferredTypeOf (letBindingTerm <$> lbindings))
          coders <- CM.mapM (constructCoder haskellLanguage (encodeTerm namespaces)) ts
          let hnames = simpleName <$> (unName . letBindingName <$> lbindings)
          hterms <- CM.zipWithM coderEncode coders (letBindingTerm <$> lbindings)

          let hbindings = L.zipWith toBinding hnames hterms
          toDecl comments hname env coder (Just $ H.LocalBindings hbindings)
        where
          toBinding hname' hterm' = H.LocalBindingValue $ simpleValueBinding hname' hterm' Nothing
      _ -> do
        hterm <- coderEncode coder term
        let vb = simpleValueBinding hname hterm bindings
        classes <- getTypeClasses typ
        htype <- encodeTypeWithClassAssertions namespaces classes typ
        let decl = H.DeclarationTypedBinding $ H.TypedBinding (H.TypeSignature hname htype) (rewriteValueBinding vb)
        return $ H.DeclarationWithComments decl comments

toTypeDeclarations :: HaskellNamespaces -> Element -> Term -> Flow Graph [H.DeclarationWithComments]
toTypeDeclarations namespaces el term = withTrace ("type element " ++ unName (elementName el)) $ do
    g <- getState
    let lname = localNameOfEager $ elementName el
    let hname = simpleName lname
    t <- coreDecodeType term

    isSer <- isSerializable el
    let deriv = H.Deriving $ if isSer
                  then rawName <$> ["Eq", "Ord", "Read", "Show"]
                  else []
    let (vars, t') = unpackLambdaType g t
    let hd = declHead hname $ L.reverse vars
    decl <- case stripType t' of
      TypeRecord rt -> do
        cons <- recordCons lname $ rowTypeFields rt
        return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordData [] hd [cons] [deriv]
      TypeUnion rt -> do
        cons <- CM.mapM (unionCons lname) $ rowTypeFields rt
        return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordData [] hd cons [deriv]
      TypeWrap (WrappedType tname wt) -> do
        cons <- newtypeCons el wt
        return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordNewtype [] hd [cons] [deriv]
      _ -> if newtypesNotTypedefs
        then do
          cons <- newtypeCons el t'
          return $ H.DeclarationData $ H.DataDeclaration H.DataDeclaration_KeywordNewtype [] hd [cons] [deriv]
        else do
          htype <- adaptTypeToHaskellAndEncode namespaces t
          return $ H.DeclarationType (H.TypeDeclaration hd htype)
    comments <- getTermDescription term
    tdecls <- if haskellGenerationOptionsIncludeTypeDefinitions defaultHaskellGenerationOptions
       then do
         decl <- typeDecl namespaces (elementName el) t
         pure [decl]
       else pure []
    return $ [H.DeclarationWithComments decl comments]
      ++ nameDecls g namespaces (elementName el) t
      ++ tdecls
  where
    declHead name vars = case vars of
      [] -> H.DeclarationHeadSimple name
      ((Name h):rest) -> H.DeclarationHeadApplication $
        H.DeclarationHead_Application (declHead name rest) (H.Variable $ simpleName h)

    newtypeCons el typ = do
        let hname = simpleName $ newtypeAccessorName $ elementName el
        htype <- adaptTypeToHaskellAndEncode namespaces typ
        let hfield = H.FieldWithComments (H.Field hname htype) Nothing
        return $ H.ConstructorWithComments
          (H.ConstructorRecord $ H.Constructor_Record (simpleName $ localNameOfEager $ elementName el) [hfield]) Nothing

    recordCons lname fields = do
        hFields <- CM.mapM toField fields
        return $ H.ConstructorWithComments (H.ConstructorRecord $ H.Constructor_Record (simpleName lname) hFields) Nothing
      where
        toField (FieldType (Name fname) ftype) = do
          let hname = simpleName $ decapitalize lname ++ capitalize fname
          htype <- adaptTypeToHaskellAndEncode namespaces ftype
          comments <- getTypeDescription ftype
          return $ H.FieldWithComments (H.Field hname htype) comments

    unionCons lname (FieldType (Name fname) ftype) = do
      comments <- getTypeDescription ftype
      let nm = capitalize lname ++ capitalize fname
      typeList <- if stripType ftype == Types.unit
        then pure []
        else do
          htype <- adaptTypeToHaskellAndEncode namespaces ftype
          return [htype]
      return $ H.ConstructorWithComments (H.ConstructorOrdinary $ H.Constructor_Ordinary (simpleName nm) typeList) comments

-- | Constructs a Hydra Type definition which can be included along with the nativized Haskell type definition
typeDecl :: HaskellNamespaces -> Name -> Type -> Flow Graph H.DeclarationWithComments
typeDecl namespaces name typ = do
    -- Note: consider constructing this coder just once, then reusing it
    coder <- constructCoder haskellLanguage (encodeTerm namespaces) typeT
    expr <- coderEncode coder finalTerm
    let rhs = H.RightHandSide expr
    let hname = simpleName $ typeNameLocal name
    let pat = applicationPattern hname []
    let decl = H.DeclarationValueBinding $ H.ValueBindingSimple $ H.ValueBinding_Simple pat rhs Nothing
    return $ H.DeclarationWithComments decl Nothing
  where
    typeName ns name = qname ns (typeNameLocal name)
    typeNameLocal name = "_" ++ localNameOfEager name ++ "_type_"
    rawTerm = coreEncodeType typ
    finalTerm = rewriteTerm rewrite rawTerm
      where
        rewrite :: (Term -> Term) -> Term -> Term
        rewrite recurse term = Y.fromMaybe (recurse term) (Decode.variant _Type term >>= forType)
          where
            forType (Field fname fterm) = if fname == _Type_record
              then Nothing -- TODO
              else if fname == _Type_variable
              then Decode.name fterm >>= forVariableType
              else Nothing
            forVariableType name = (\ns -> TermVariable $ qname ns $ "_" ++ local ++ "_type_") <$> mns
              where
                (QualifiedName mns local) = qualifyNameEager name
