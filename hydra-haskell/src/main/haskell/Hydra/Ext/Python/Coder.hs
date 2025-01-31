module Hydra.Ext.Python.Coder (moduleToPython) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Ext.Python.Language
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
import qualified Hydra.Ext.Python.Syntax as Py
import Hydra.Ext.Python.Utils
import qualified Hydra.Ext.Python.Serde as PySer
import qualified Hydra.Lib.Strings as Strings
import qualified Hydra.Dsl.Types as Types
import Hydra.Dsl.ShorthandTypes
import Hydra.Lib.Io
import Hydra.Tools.Formatting
import qualified Hydra.Decode as Decode

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y

-- Temporary macros for Python code generation
_useFutureAnnotations_ = True

data PythonEnvironment = PythonEnvironment {
  pythonEnvironmentNamespaces :: Namespaces Py.DottedName,
  pythonEnvironmentBoundTypeVariables :: ([Name], M.Map Name Py.Name)}

-- | Temporary metadata which is used to create the header section of a Python file
data PythonModuleMetadata = PythonModuleMetadata {
  pythonModuleMetadataTypeVariables :: S.Set Name,
  pythonModuleMetadataUsesAnnotated :: Bool,
  pythonModuleMetadataUsesCallable :: Bool,
  pythonModuleMetadataUsesDataclass :: Bool,
  pythonModuleMetadataUsesEnum :: Bool,
  pythonModuleMetadataUsesGeneric :: Bool,
  pythonModuleMetadataUsesTypeVar :: Bool,
  pythonModuleMetadataUsesNode :: Bool}

encodeFieldName :: Name -> Py.Name
encodeFieldName fname = Py.Name $ sanitizePythonName $
  convertCase CaseConventionCamel CaseConventionLowerSnake $ unName fname

encodeFieldType :: PythonEnvironment -> FieldType -> Flow Graph Py.Statement
encodeFieldType env (FieldType fname ftype) = do
  comment <- getTypeDescription ftype
  let pyName = Py.SingleTargetName $ encodeFieldName fname
  pyType <- annotatedExpression comment <$> encodeType env ftype
  return $ pyAssignmentToPyStatement $ Py.AssignmentTyped $ Py.TypedAssignment pyName pyType Nothing

encodeFunctionType :: PythonEnvironment -> FunctionType -> Flow Graph Py.Expression
encodeFunctionType env ft = do
    pydoms <- CM.mapM encode doms
    pycod <- encode cod
    return $ pyPrimaryToPyExpression $ primaryWithSlices (pyNameToPyPrimary $ Py.Name "Callable")
      (pyPrimaryToPySlice $ Py.PrimarySimple $ Py.AtomList $ pyList pydoms)
      [Py.SliceOrStarredExpressionSlice $ pyExpressionToPySlice pycod]
  where
    encode = encodeType env
    (doms, cod) = gatherParams [] ft
    gatherParams rdoms (FunctionType dom cod) = case stripType cod of
      TypeFunction ft2 -> gatherParams (dom:rdoms) ft2
      _ -> (L.reverse (dom:rdoms), cod)

encodeApplicationType :: PythonEnvironment -> ApplicationType -> Flow Graph Py.Expression
encodeApplicationType env at = do
    pybody <- encodeType env body
    pyargs <- CM.mapM (encodeType env) args
    return $ primaryAndParams (pyExpressionToPyPrimary pybody) pyargs
  where
    (body, args) = gatherParams (TypeApplication at) []
    gatherParams t ps = case stripType t of
      TypeApplication (ApplicationType lhs rhs) -> gatherParams lhs (rhs:ps)
      _ -> (t, ps)

encodeDefinition :: PythonEnvironment -> Definition -> Flow Graph [Py.Statement]
encodeDefinition env def = case def of
  DefinitionTerm name term typ -> withTrace ("data element " ++ unName name) $ do
    comment <- fmap normalizeComment <$> getTermDescription term
    encodeTermAssignment env name term typ comment
  DefinitionType name typ -> withTrace ("type element " ++ unName name) $ do
    comment <- fmap normalizeComment <$> getTypeDescription typ
    encodeTypeAssignment env name typ comment

encodeElimination :: PythonEnvironment -> Elimination -> Flow s Py.Expression
encodeElimination env elm = case elm of
--  EliminationRecord (Projection _ fname) ->
  _ -> fail $ "unsupported elimination variant: " ++ show (eliminationVariant elm)

encodeFloatValue :: FloatValue -> Flow s Py.Expression
encodeFloatValue fv = case fv of
  FloatValueBigfloat f -> pure $ pyAtomToPyExpression $ Py.AtomNumber $ Py.NumberFloat f
  _ -> fail $ "unsupported floating point type: " ++ show (floatValueType fv)

encodeFunction :: PythonEnvironment -> Function -> Flow s Py.Expression
encodeFunction env f = case f of
  FunctionElimination elm -> encodeElimination env elm
  FunctionLambda (Lambda var _ body) -> do
    pbody <- encodeTerm env body
    return $ Py.ExpressionLambda $ Py.Lambda (Py.LambdaParameters Nothing [] [] $ Just $ Py.LambdaStarEtcKwds $ Py.LambdaKwds $ Py.LambdaParamNoDefault $ encodeName env var) pbody
  FunctionPrimitive name -> pure $ pyNameToPyExpression $ encodeName env name

encodeIntegerValue :: IntegerValue -> Flow s Py.Expression
encodeIntegerValue iv = case iv of
  IntegerValueBigint i -> pure $ pyAtomToPyExpression $ Py.AtomNumber $ Py.NumberInteger i
  _ -> fail $ "unsupported integer type: " ++ show (integerValueType iv)

encodeLambdaType :: PythonEnvironment -> LambdaType -> Flow Graph Py.Expression
encodeLambdaType env lt = do
    pybody <- encodeType env body
    return $ primaryAndParams (pyExpressionToPyPrimary pybody) (pyNameToPyExpression . Py.Name . unName <$> params)
  where
    (body, params) = gatherParams (TypeLambda lt) []
    gatherParams t ps = case stripType t of
      TypeLambda (LambdaType name body) -> gatherParams body (name:ps)
      _ -> (t, L.reverse ps)

encodeLiteral :: Literal -> Flow s Py.Expression
encodeLiteral lit = case lit of
  LiteralBoolean b -> pure $ pyAtomToPyExpression $ if b then Py.AtomTrue else Py.AtomFalse
  LiteralFloat f -> encodeFloatValue f
  LiteralInteger i -> encodeIntegerValue i
  LiteralString s -> pure $ stringToPyExpression Py.QuoteStyleDouble s
  _ -> fail $ "unsupported literal variant: " ++ show (literalVariant lit)

encodeLiteralType :: LiteralType -> Flow Graph Py.Expression
encodeLiteralType lt = do
    name <- Py.Name <$> findName
    return $ pyNameToPyExpression name
  where
    findName = case lt of
      LiteralTypeBinary -> pure "bytes"
      LiteralTypeBoolean -> pure "bool"
      LiteralTypeFloat ft -> case ft of
        FloatTypeFloat64 -> pure "float"
        _ -> fail $ "unsupported floating-point type: " ++ show ft
      LiteralTypeInteger it -> case it of
        IntegerTypeBigint -> pure "int"
        _ -> fail $ "unsupported integer type: " ++ show it
      LiteralTypeString -> pure "str"

encodeModule :: Module -> Flow Graph Py.Module
encodeModule mod = do
    defs <- adaptedModuleDefinitions pythonLanguage mod
    let namespaces = namespacesForDefinitions encodeNamespace (moduleNamespace mod) defs
    let env = PythonEnvironment {
              pythonEnvironmentNamespaces = namespaces,
              pythonEnvironmentBoundTypeVariables = ([], M.empty)}
    defStmts <- L.concat <$> (CM.mapM (encodeDefinition env) defs)
    let meta = gatherMetadata defs
    let tvars = pythonModuleMetadataTypeVariables meta
    let importStmts = imports namespaces meta
    let tvarStmts = tvarStmt . encodeTypeVariable <$> S.toList tvars
    let mc = tripleQuotedString . normalizeComment <$> moduleDescription mod
    let commentStmts = case normalizeComment <$> moduleDescription mod of
                       Nothing -> []
                       Just c -> [commentStatement c]
    let body = L.filter (not . L.null) [commentStmts, importStmts, tvarStmts] ++ (singleton <$> defStmts)
    return $ Py.Module body
  where
    singleton s = [s]
    tvarStmt name = assignmentStatement name $ functionCall (pyNameToPyPrimary $ Py.Name "TypeVar")
      [doubleQuotedString $ Py.unName name]
    imports namespaces meta = pySimpleStatementToPyStatement . Py.SimpleStatementImport <$> (standardImports ++ domainImports)
      where
        domainImports = toImport <$> names
          where
            names = L.sort $ M.elems $ namespacesMapping namespaces
            toImport ns = Py.ImportStatementName $ Py.ImportName [Py.DottedAsName ns Nothing]
        standardImports = toImport <$> (Y.catMaybes (simplifyPair <$> pairs))
          where
            simplifyPair (a, symbols) = if L.null rem then Nothing else Just (a, rem)
              where
                rem = Y.catMaybes symbols
            pairs = [
                ("__future__", [if _useFutureAnnotations_ then Just "annotations" else Nothing]),
                ("collections.abc", [
                  cond "Callable" $ pythonModuleMetadataUsesCallable meta]),
                ("dataclasses", [
                  cond "dataclass" $ pythonModuleMetadataUsesDataclass meta]),
                ("enum", [
                  cond "Enum" $ pythonModuleMetadataUsesEnum meta]),
                ("hydra.dsl.python", [
                  cond "Node" $ pythonModuleMetadataUsesNode meta]),
                ("typing", [
                  cond "Annotated" $ pythonModuleMetadataUsesAnnotated meta,
                  cond "Generic" $ pythonModuleMetadataUsesGeneric meta,
                  cond "TypeVar" $ pythonModuleMetadataUsesTypeVar meta])]
              where
                cond name b = if b then Just name else Nothing
            toImport (modName, symbols) = Py.ImportStatementFrom $
                Py.ImportFrom [] (Just $ Py.DottedName [Py.Name modName]) $
                  Py.ImportFromTargetsSimple (forSymbol <$> symbols)
              where
                forSymbol s = Py.ImportFromAsName (Py.Name s) Nothing

encodeName :: PythonEnvironment -> Name -> Py.Name
encodeName env name = case M.lookup name (snd $ pythonEnvironmentBoundTypeVariables env) of
    Just n -> n
    Nothing -> if ns == Just focusNs
      then Py.Name $ if _useFutureAnnotations_ then local else PySer.escapePythonString True local
      else Py.Name $ L.intercalate "." $ Strings.splitOn "/" $ unName name
  where
    focusNs = fst $ namespacesFocus $ pythonEnvironmentNamespaces env
    QualifiedName ns local = qualifyNameEager name

encodeNamespace :: Namespace -> Py.DottedName
encodeNamespace ns = Py.DottedName (Py.Name <$> (Strings.splitOn "/" $ unNamespace ns))

encodeRecordType :: PythonEnvironment -> Name -> RowType -> Maybe String -> Flow Graph Py.Statement
encodeRecordType env name (RowType _ tfields) comment = do
    pyFields <- CM.mapM (encodeFieldType env) tfields
    let body = indentedBlock comment [pyFields]
    return $ pyClassDefinitionToPyStatement $
      Py.ClassDefinition (Just decs) (Py.Name lname) [] args body
  where
    (tparamList, tparamMap) = pythonEnvironmentBoundTypeVariables env
    lname = localNameOfEager name
    args = fmap (\a -> pyExpressionsToPyArgs [a]) $ genericArg tparamList
    decs = Py.Decorators [pyNameToPyNamedExpression $ Py.Name "dataclass"]

encodeTerm :: PythonEnvironment -> Term -> Flow s Py.Expression
encodeTerm env term = case fullyStripTerm term of
    TermApplication (Application fun arg) -> do
      pfun <- encode fun
      parg <- encode arg
      return $ functionCall (pyExpressionToPyPrimary pfun) [parg]
    TermFunction f -> encodeFunction env f
    TermList els -> pyAtomToPyExpression . Py.AtomList . pyList <$> CM.mapM encode els
    TermLiteral lit -> encodeLiteral lit
    TermOptional mt -> case mt of
      Nothing -> pure $ pyNameToPyExpression pyNone
      Just term1 -> encode term1
    TermRecord (Record tname fields) -> do
      pargs <- CM.mapM (encode . fieldTerm) fields
      return $ functionCall (pyNameToPyPrimary $ encodeName env tname) pargs
    TermUnion (Injection tname field) -> do
      parg <- encode $ fieldTerm field
      return $ functionCall (pyNameToPyPrimary $ variantName True env tname (fieldName field)) [parg]
    TermVariable name -> pure $ variableReference env name
    TermWrap (WrappedTerm tname term1) -> do
      parg <- encode term1
      return $ functionCall (pyNameToPyPrimary $ encodeName env tname) [parg]
    t -> fail $ "unsupported term variant: " ++ show (termVariant t)
  where
    encode = encodeTerm env

encodeTermAssignment :: PythonEnvironment -> Name -> Term -> Type -> Maybe String -> Flow s [Py.Statement]
encodeTermAssignment env name term _ comment = do
  expr <- encodeTerm env term
  return [annotatedStatement comment $ assignmentStatement (Py.Name $ localNameOfEager name) expr]

encodeType :: PythonEnvironment -> Type -> Flow Graph Py.Expression
encodeType env typ = case stripType typ of
    TypeApplication at -> encodeApplicationType env at
    TypeFunction ft -> encodeFunctionType env ft
    TypeLambda lt -> encodeLambdaType env lt
    TypeList et -> nameAndParams (Py.Name "list") . L.singleton <$> encode et
    TypeMap (MapType kt vt) -> do
      pykt <- encode kt
      pyvt <- encode vt
      return $ nameAndParams (Py.Name "dict") [pykt, pyvt]
    TypeLiteral lt -> encodeLiteralType lt
    TypeOptional et -> orNull . pyExpressionToPyPrimary <$> encode et
    TypeRecord rt -> pure $ if isUnitType (TypeRecord rt)
      then pyNameToPyExpression pyNone
      else variableReference env $ rowTypeTypeName rt
    TypeSet et -> nameAndParams (Py.Name "set") . L.singleton <$> encode et
    TypeUnion rt -> pure $ variableReference env $ rowTypeTypeName rt
    TypeVariable name -> pure $ variableReference env name
    TypeWrap (WrappedType name _) -> pure $ variableReference env name
    _ -> dflt
  where
    encode = encodeType env
    dflt = pure $ doubleQuotedString $ "type = " ++ show (stripType typ)

encodeTypeAssignment :: PythonEnvironment -> Name -> Type -> Maybe String -> Flow Graph [Py.Statement]
encodeTypeAssignment env name typ comment = encode env typ
  where
    encode env typ = case stripType typ of
      TypeLambda (LambdaType var body) -> encode newEnv body
        where
          (tparamList, tparamMap) = pythonEnvironmentBoundTypeVariables env
          newEnv = env {pythonEnvironmentBoundTypeVariables = (tparamList ++ [var], M.insert var (encodeTypeVariable var) tparamMap)}
      TypeRecord rt -> single <$> encodeRecordType env name rt comment
      TypeUnion rt -> encodeUnionType env name rt comment
--      TypeWrap (WrappedType _ t) -> (single . newtypeStatement (Py.Name $ localNameOfEager name) comment) <$> encodeType env t
      TypeWrap (WrappedType _ t) -> single <$> encodeWrappedType env name t comment
      t -> singleTypedef env <$> encodeType env t
    single st = [st]
    singleTypedef env e = single $ typeAliasStatement (Py.Name $ sanitizePythonName $ localNameOfEager name) tparams comment e
      where
        tparams = environmentTypeParameters env

encodeTypeQuoted :: PythonEnvironment -> Type -> Flow Graph Py.Expression
encodeTypeQuoted env typ = do
  pytype <- encodeType env typ
  return $ if S.null (freeVariablesInType typ)
    then pytype
    else doubleQuotedString $ printExpr $ PySer.encodeExpression pytype

encodeTypeVariable :: Name -> Py.Name
encodeTypeVariable = Py.Name . capitalize . unName

encodeUnionType :: PythonEnvironment -> Name -> RowType -> Maybe String -> Flow Graph [Py.Statement]
encodeUnionType env name rt@(RowType _ tfields) comment = if isEnumType rt then asEnum else asUnion
  where
    asEnum = do
        vals <- CM.mapM toVal tfields
        let body = indentedBlock comment vals
        return [pyClassDefinitionToPyStatement $ Py.ClassDefinition Nothing (Py.Name lname) [] args body]
      where
        args = Just $ pyExpressionsToPyArgs [pyNameToPyExpression $ Py.Name "Enum"]
        toVal (FieldType fname ftype) = do
          fcomment <- fmap normalizeComment <$> getTypeDescription ftype
          return $ Y.catMaybes [
            Just $ assignmentStatement (enumVariantName $ unName fname) (doubleQuotedString $ unName fname),
            pyExpressionToPyStatement . tripleQuotedString <$> fcomment]
        enumVariantName fname = Py.Name $ convertCase CaseConventionCamel CaseConventionUpperSnake fname
    asUnion = do
      fieldStmts <- CM.mapM toFieldStmt tfields
      return $ fieldStmts ++ [unionStmt]
      where
        toFieldStmt (FieldType fname ftype) = do
            comment <- fmap normalizeComment <$> getTypeDescription ftype
            ptypeQuoted <- encodeTypeQuoted env ftype
            let body = indentedBlock comment []
            return $ pyClassDefinitionToPyStatement $
              Py.ClassDefinition
                Nothing
                (variantName False env name fname)
                (pyNameToPyTypeParameter <$> fieldParams ftype)
                (Just $ variantArgs ptypeQuoted [])
                body
        unionStmt = typeAliasStatement
            (Py.Name $ sanitizePythonName lname)
            tparams
            comment
            (orExpression (alt <$> tfields))
          where
            tparams = environmentTypeParameters env
            alt (FieldType fname ftype) = if L.null tparams
                then namePrim
                else primaryWithExpressionSlices namePrim (pyNameToPyExpression <$> tparams)
              where
                tparams = fieldParams ftype
                namePrim = pyNameToPyPrimary $ variantName False env name fname
        fieldParams ftype = encodeTypeVariable <$> findTypeParams env ftype
    lname = localNameOfEager name

encodeWrappedType :: PythonEnvironment -> Name -> Type -> Maybe String -> Flow Graph Py.Statement
encodeWrappedType env name typ comment = do
    ptypeQuoted <- encodeTypeQuoted env typ
    let body = indentedBlock comment []
    return $ pyClassDefinitionToPyStatement $
      Py.ClassDefinition
        Nothing
        (Py.Name $ sanitizePythonName lname)
        (pyNameToPyTypeParameter . encodeTypeVariable <$> findTypeParams env typ)
        (Just $ variantArgs ptypeQuoted tparamList)
        body
  where
    (tparamList, tparamMap) = pythonEnvironmentBoundTypeVariables env
    lname = localNameOfEager name

environmentTypeParameters :: PythonEnvironment -> [Py.TypeParameter]
environmentTypeParameters env = pyNameToPyTypeParameter . encodeTypeVariable <$> (fst $ pythonEnvironmentBoundTypeVariables env)

findTypeParams :: PythonEnvironment -> Type -> [Name]
findTypeParams env typ = L.filter isBound $ S.toList $ freeVariablesInType typ
  where
    isBound v = Y.isJust $ M.lookup v $ snd $ pythonEnvironmentBoundTypeVariables env

gatherMetadata :: [Definition] -> PythonModuleMetadata
gatherMetadata defs = checkTvars $ L.foldl addDef start defs
  where
    checkTvars meta = meta {pythonModuleMetadataUsesTypeVar = not $ S.null $ pythonModuleMetadataTypeVariables meta}
    start = PythonModuleMetadata {
      pythonModuleMetadataTypeVariables = S.empty,
      pythonModuleMetadataUsesAnnotated = False,
      pythonModuleMetadataUsesCallable = False,
      pythonModuleMetadataUsesDataclass = False,
      pythonModuleMetadataUsesEnum = False,
      pythonModuleMetadataUsesGeneric = False,
      pythonModuleMetadataUsesTypeVar = False,
      pythonModuleMetadataUsesNode = False}
    addDef meta def = case def of
      DefinitionTerm _ _ _ -> meta
      DefinitionType _ typ -> foldOverType TraversalOrderPre extendMeta meta3 typ
        where
          tvars = pythonModuleMetadataTypeVariables meta
          meta3 = case stripType typ of
            TypeWrap _ -> meta2 {pythonModuleMetadataUsesNode = True}
            _ -> meta2
          meta2 = meta {pythonModuleMetadataTypeVariables = newTvars tvars typ}
            where
              newTvars s t = case stripType t of
                TypeLambda (LambdaType v body) -> newTvars (S.insert v s) body
                _ -> s
          extendMeta meta t = case t of
            TypeFunction _ -> meta {pythonModuleMetadataUsesCallable = True}
            TypeLambda (LambdaType _ body) -> case baseType body of
                TypeRecord _ -> meta {pythonModuleMetadataUsesGeneric = True}
                _ -> meta
              where
                baseType t = case stripType t of
                  TypeLambda (LambdaType _ body2) -> baseType body2
                  t2 -> t2
            TypeRecord (RowType _ fields) -> meta {
                pythonModuleMetadataUsesAnnotated = L.foldl checkForAnnotated (pythonModuleMetadataUsesAnnotated meta) fields,
                pythonModuleMetadataUsesDataclass = pythonModuleMetadataUsesDataclass meta || not (L.null fields)}
              where
                checkForAnnotated b (FieldType _ ft) = b || hasTypeDescription ft
            TypeUnion rt@(RowType _ fields) -> if isEnumType rt
                then meta {pythonModuleMetadataUsesEnum = True}
                else meta {
                  pythonModuleMetadataUsesNode = pythonModuleMetadataUsesNode meta || (not $ L.null fields)}
              where
                checkForLiteral b (FieldType _ ft) = b || isUnitType (stripType ft)
                checkForNewType b (FieldType _ ft) = b || not (isUnitType (stripType ft))
            _ -> meta

genericArg :: [Name] -> Y.Maybe Py.Expression
genericArg tparamList = if L.null tparamList
  then Nothing
  else Just $ pyPrimaryToPyExpression $ primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Generic")
    (pyNameToPyExpression . encodeTypeVariable <$> tparamList)

moduleToPython :: Module -> Flow Graph (M.Map FilePath String)
moduleToPython mod = do
  file <- encodeModule mod
  let s = printExpr $ parenthesize $ PySer.encodeModule file
  let path = namespaceToFilePath False (FileExtension "py") $ moduleNamespace mod
  return $ M.fromList [(path, s)]

sanitizePythonName :: String -> String
sanitizePythonName = sanitizeWithUnderscores pythonReservedWords

variableReference :: PythonEnvironment -> Name -> Py.Expression
variableReference env name = pyNameToPyExpression $ encodeName env name

variantArgs :: Py.Expression -> [Name] -> Py.Args
variantArgs ptype tparams = pyExpressionsToPyArgs $ Y.catMaybes [
    Just $ pyPrimaryToPyExpression $
      primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Node") [ptype],
    genericArg tparams]

variantName :: Bool -> PythonEnvironment -> Name -> Name -> Py.Name
variantName qual env tname fname = if qual
    then encodeName env $ unqualifyName $ QualifiedName mns vname
    else Py.Name vname
  where
    (QualifiedName mns local) = qualifyNameEager tname
    vname = sanitizePythonName $ local ++ (capitalize $ unName fname)
