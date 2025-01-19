module Hydra.Ext.Python.Coder (moduleToPython) where

import Hydra.Kernel
import Hydra.Adapters
import Hydra.Ext.Python.Language
import Hydra.Dsl.Terms
import Hydra.Tools.Serialization
import qualified Hydra.Ext.Python.Syntax as Py
import Hydra.Ext.Python.Utils
import Hydra.Ext.Python.Serde hiding (encodeName, encodeTerm)
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

data PythonEnvironment = PythonEnvironment {
  pythonEnvironmentNamespaces :: PythonNamespaces,
  pythonEnvironmentBoundTypeVariables :: TypeParams}

-- | Temporary metadata which is used to create the header section of a Python file
data PythonModuleMetadata = PythonModuleMetadata {
  pythonModuleMetadataTypeVariables :: S.Set Name,
  pythonModuleMetadataUsesAnnotated :: Bool,
  pythonModuleMetadataUsesCallable :: Bool,
  pythonModuleMetadataUsesDataclass :: Bool,
  pythonModuleMetadataUsesGeneric :: Bool,
  pythonModuleMetadataUsesLiteral :: Bool,
  pythonModuleMetadataUsesNewType :: Bool,
  pythonModuleMetadataUsesTypeVar :: Bool}

type PythonNamespaces = Namespaces Py.DottedName

type TypeParams = ([Py.Name], M.Map Name Py.Name)

-- TODO: use these
constantForFieldName tname fname = toUpperCase (localNameOfEager tname) ++ "_" ++ toUpperCase (unName fname)
constantForTypeName tname = toUpperCase $ localNameOfEager tname

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
      (pyPrimaryToPySlice $ Py.PrimarySimple $ Py.AtomList $
        Py.List (Py.StarNamedExpressionSimple . Py.NamedExpressionSimple <$> pydoms))
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

encodeLambdaType :: PythonEnvironment -> LambdaType -> Flow Graph Py.Expression
encodeLambdaType env lt = do
    pybody <- encodeType env body
    return $ primaryAndParams (pyExpressionToPyPrimary pybody) (pyNameToPyExpression . Py.Name . unName <$> params)
  where
    (body, params) = gatherParams (TypeLambda lt) []
    gatherParams t ps = case stripType t of
      TypeLambda (LambdaType name body) -> gatherParams body (name:ps)
      _ -> (t, L.reverse ps)

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

encodeName :: PythonEnvironment -> Name -> Py.Name
encodeName env name = case M.lookup name (snd $ pythonEnvironmentBoundTypeVariables env) of
    Just n -> n
    Nothing -> if ns == Just focusNs
      then Py.Name local
      else Py.Name $ L.intercalate "." $ Strings.splitOn "/" $ unName name
  where
    focusNs = fst $ namespacesFocus $ pythonEnvironmentNamespaces env
    QualifiedName ns local = qualifyNameEager name

encodeNamespace :: Namespace -> Py.DottedName
encodeNamespace ns = Py.DottedName (Py.Name <$> (Strings.splitOn "/" $ unNamespace ns))

encodeRecordType :: PythonEnvironment -> Name -> RowType -> Maybe String -> Flow Graph Py.Statement
encodeRecordType env name (RowType _ tfields) comment = do
    pyFields <- CM.mapM (encodeFieldType env) tfields
    let body = Py.BlockIndented pyFields
    return $ Py.StatementCompound $ Py.CompoundStatementClassDef $
      Py.ClassDefinition (Just decs) (Py.Name lname) [] args comment body
  where
    (tparamList, tparamMap) = pythonEnvironmentBoundTypeVariables env
    lname = localNameOfEager name
    args = if L.null tparamList
      then Nothing
      else Just $ Py.Args [Py.PosArgExpression $ pyPrimaryToPyExpression $
        primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Generic") (pyNameToPyExpression <$> tparamList)] [] []
    decs = Py.Decorators [pyNameToPyNamedExpression $ Py.Name "dataclass"]

encodeTerm :: PythonEnvironment -> Term -> Flow Graph Py.Expression
encodeTerm env term = fail "not yet implemented"

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
    TypeRecord rt -> if isUnitType (TypeRecord rt)
      then pure $ pyNameToPyExpression $ Py.Name "None"
      else variableReference $ rowTypeTypeName rt
    TypeSet et -> nameAndParams (Py.Name "set") . L.singleton <$> encode et
    TypeUnion rt -> variableReference $ rowTypeTypeName rt
    TypeVariable name -> variableReference name
    _ -> dflt
  where
    encode = encodeType env
    dflt = pure $ stringToPyExpression $ "type = " ++ show (stripType typ)
    variableReference name = pure $ pyNameToPyExpression $ encodeName env name

encodeTypeAssignment :: PythonEnvironment -> Name -> Type -> Maybe String -> Flow Graph [Py.Statement]
encodeTypeAssignment env name typ comment = encode env typ
  where
    encode env typ = case stripType typ of
      TypeLambda (LambdaType var body) -> encode newEnv body
        where
          pyvar = encodeTypeVariable var
          (tparamList, tparamMap) = pythonEnvironmentBoundTypeVariables env
          newEnv = env {pythonEnvironmentBoundTypeVariables = (tparamList ++ [pyvar], M.insert var pyvar tparamMap)}
      TypeRecord rt -> single <$> encodeRecordType env name rt comment
      TypeUnion rt -> encodeUnionType env name rt comment
      TypeWrap (WrappedType _ t) -> singleNewtype <$> encodeType env t
      t -> singleTypedef <$> encodeType env t
    single st = [st]
    singleNewtype e = single $ newtypeStatement (Py.Name $ localNameOfEager name) comment e
    singleTypedef e = single $ typeAliasStatement (Py.Name $ sanitizePythonName $ localNameOfEager name) comment e

encodeTypeVariable :: Name -> Py.Name
encodeTypeVariable = Py.Name . capitalize . unName

-- TODO: consider producing Python enums where appropriate
encodeUnionType :: PythonEnvironment -> Name -> RowType -> Maybe String -> Flow Graph [Py.Statement]
encodeUnionType env name (RowType _ tfields) comment = do
    fieldStmts <- CM.mapM toFieldStmt tfields
    return $ fieldStmts ++ [unionStmt]
  where
    toFieldStmt (FieldType fname ftype) = do
        fcomment <- getTypeDescription ftype
        if isUnitType (stripType ftype)
          then pure $ assignmentStatement (variantName fname) $
            pyPrimaryToPyExpression $ primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Literal")
              [stringToPyExpression $ unName fname]
          else newtypeStatement (variantName fname) fcomment <$> encodeType env ftype
    unionStmt = typeAliasStatement (Py.Name $ sanitizePythonName $ localNameOfEager name) comment $
      orExpression (pyNameToPyPrimary . variantName . fieldTypeName <$> tfields)
    variantName fname = Py.Name $ sanitizePythonName $ (localNameOfEager name) ++ (capitalize $ unName fname)

gatherMetadata :: [Definition] -> PythonModuleMetadata
gatherMetadata defs = checkTvars $ L.foldl addDef start defs
  where
    checkTvars meta = meta {pythonModuleMetadataUsesTypeVar = not $ S.null $ pythonModuleMetadataTypeVariables meta}
    start = PythonModuleMetadata {
      pythonModuleMetadataTypeVariables = S.empty,
      pythonModuleMetadataUsesAnnotated = False,
      pythonModuleMetadataUsesCallable = False,
      pythonModuleMetadataUsesDataclass = False,
      pythonModuleMetadataUsesGeneric = False,
      pythonModuleMetadataUsesLiteral = False,
      pythonModuleMetadataUsesNewType = False,
      pythonModuleMetadataUsesTypeVar = False}
    addDef meta def = case def of
      DefinitionTerm _ _ _ -> meta
      DefinitionType _ typ -> foldOverType TraversalOrderPre extendMeta newMeta typ
        where
          tvars = pythonModuleMetadataTypeVariables meta
          newMeta = meta {pythonModuleMetadataTypeVariables = newTvars tvars typ}
            where
              newTvars s t = case stripType t of
                TypeLambda (LambdaType v body) -> newTvars (S.insert v s) body
                _ -> s
          extendMeta meta t = case t of
            TypeFunction _ -> meta {pythonModuleMetadataUsesCallable = True}
            TypeLambda _ -> meta {pythonModuleMetadataUsesGeneric = True}
            TypeRecord (RowType _ fields) -> meta {
                pythonModuleMetadataUsesAnnotated = L.foldl checkForAnnotated (pythonModuleMetadataUsesAnnotated meta) fields,
                pythonModuleMetadataUsesDataclass = pythonModuleMetadataUsesDataclass meta || not (L.null fields)}
              where
                checkForAnnotated b (FieldType _ ft) = b || hasTypeDescription ft
            TypeUnion (RowType _ fields) -> meta {
                pythonModuleMetadataUsesLiteral = L.foldl checkForLiteral (pythonModuleMetadataUsesLiteral meta) fields,
                pythonModuleMetadataUsesNewType = L.foldl checkForNewType (pythonModuleMetadataUsesNewType meta) fields}
              where
                checkForLiteral b (FieldType _ ft) = b || isUnitType (stripType ft)
                checkForNewType b (FieldType _ ft) = b || not (isUnitType (stripType ft))
            TypeWrap _ -> meta {pythonModuleMetadataUsesNewType = True}
            _ -> meta

moduleToPythonModule :: Module -> Flow Graph Py.Module
moduleToPythonModule mod = do
    namespaces <- namespacesForModule mod -- TODO: use the adapted definitions, not the raw module
    let env = PythonEnvironment {
              pythonEnvironmentNamespaces = namespaces,
              pythonEnvironmentBoundTypeVariables = ([], M.empty)}
    defs <- adaptedModuleDefinitions pythonLanguage mod
    let meta = gatherMetadata defs
    let tvars = pythonModuleMetadataTypeVariables meta
    defStmts <- L.concat <$> (CM.mapM (createDeclarations env) defs)
    let tvarStmts = tvarStmt . encodeTypeVariable <$> S.toList tvars
    let stmts = tvarStmts ++ defStmts
    let mc = normalizeComment <$> moduleDescription mod
    return $ Py.Module (imports namespaces meta) mc stmts
  where
    createDeclarations env def = case def of
      DefinitionTerm name term typ -> withTrace ("data element " ++ unName name) $
        return [pySimpleStatementToPyStatement Py.SimpleStatementContinue] -- TODO
      DefinitionType name typ -> withTrace ("type element " ++ unName name) $ do
        comment <- fmap normalizeComment <$> getTypeDescription typ
        encodeTypeAssignment env name typ comment
    createDataDeclaration name term typ = fail "oops"
    createTypeDeclaration name typ = fail "oops"
    tvarStmt name = assignmentStatement name $ functionCall (pyNameToPyPrimary $ Py.Name "TypeVar")
      [stringToPyExpression $ Py.unName name]
    imports namespaces meta = standardImports ++ domainImports
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
                ("__future__", [Just "annotations"]),
                ("collections.abc", [
                  cond "Callable" $ pythonModuleMetadataUsesCallable meta]),
                ("typing", [
                  cond "Annotated" $ pythonModuleMetadataUsesAnnotated meta,
                  cond "Generic" $ pythonModuleMetadataUsesGeneric meta,
                  cond "Literal" $ pythonModuleMetadataUsesLiteral meta,
                  cond "NewType" $ pythonModuleMetadataUsesNewType meta,
                  cond "TypeVar" $ pythonModuleMetadataUsesTypeVar meta]),
                ("dataclasses", [
                  cond "dataclass" $ pythonModuleMetadataUsesDataclass meta])]
              where
                cond name b = if b then Just name else Nothing
            toImport (modName, symbols) = Py.ImportStatementFrom $
              Py.ImportFrom [] (Just $ Py.DottedName [Py.Name modName]) $
                Py.ImportFromTargetsSimple (forSymbol <$> symbols)
              where
                forSymbol s = Py.ImportFromAsName (Py.Name s) Nothing

moduleToPython :: Module -> Flow Graph (M.Map FilePath String)
moduleToPython mod = do
  file <- moduleToPythonModule mod
  let s = printExpr $ parenthesize $ encodeModule file
  let path = namespaceToFilePath False (FileExtension "py") $ moduleNamespace mod
  return $ M.fromList [(path, s)]

namespacesForModule :: Module -> Flow Graph PythonNamespaces
namespacesForModule mod = do
    nss <- moduleDependencyNamespaces True True False False mod
    return $ Namespaces (toPair focusNs) $ M.fromList (toPair <$> S.toList nss)
  where
    focusNs = moduleNamespace mod
    toPair ns = (ns, encodeNamespace ns)

sanitizePythonName :: String -> String
sanitizePythonName = sanitizeWithUnderscores pythonReservedWords
