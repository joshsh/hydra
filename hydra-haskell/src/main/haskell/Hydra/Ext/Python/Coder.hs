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


type PythonNamespaces = Namespaces Py.DottedName

type TypeParams = ([(Name, Py.Name)], M.Map Name Py.Name)

-- TODO: use these
constantForFieldName tname fname = toUpperCase (localNameOfEager tname) ++ "_" ++ toUpperCase (unName fname)
constantForTypeName tname = toUpperCase $ localNameOfEager tname

constructModule :: PythonNamespaces
  -> Module
  -> M.Map Type (Coder Graph Graph Term Py.Expression)
  -> [(Element, TypedTerm)] -> Flow Graph Py.Module
constructModule namespaces mod coders pairs = do
    g <- getState
    pairs <- CM.mapM (createDeclarations g) pairs
    let defStmts = L.concat (fst <$> pairs)
    let tvars = S.toList $ L.foldl S.union S.empty (snd <$> pairs)

    -- TODO: this may be more than we need, as the TypeVar statements may only be needed for NewType declarations, not for dataclasses
    let tvarStmts = tvarStmt <$> tvars

    let stmts = tvarStmts ++ defStmts
    let mc = moduleDescription mod
    return $ Py.Module imports mc stmts
  where
    tvarStmt name = assignmentStatement name $ functionCall (pyNameToPyPrimary $ Py.Name "TypeVar")
      [stringToPyExpression $ Py.unName name]

    createDeclarations g pair@(el, TypedTerm term typ) = if isType typ
      then toTypeDeclarations namespaces el term
      else do
        st <- toDataDeclarations coders namespaces pair
        return (st, S.empty)

    imports = standardImports ++ domainImports
      where
        domainImports = toImport <$> names
          where
            names = L.sort $ M.elems $ namespacesMapping namespaces
            toImport ns = Py.ImportStatementName $ Py.ImportName [Py.DottedAsName ns Nothing]
        standardImports = toImport <$> pairs
          where
            pairs = [
              ("__future__", ["annotations"]),
              ("typing", ["Annotated", "Callable", "Literal", "NewType", "TypeVar"]),
              ("dataclasses", ["dataclass", "field"])]
            toImport (modName, symbols) = Py.ImportStatementFrom $
              Py.ImportFrom [] (Just $ Py.DottedName [Py.Name modName]) $
                Py.ImportFromTargetsSimple (forSymbol <$> symbols)
              where
                forSymbol s = Py.ImportFromAsName (Py.Name s) Nothing

encodeFieldName :: Name -> Py.Name
encodeFieldName fname = Py.Name $ convertCase CaseConventionCamel CaseConventionLowerSnake $ unName fname

encodeFieldType :: PythonNamespaces -> TypeParams -> FieldType -> Flow Graph Py.Statement
encodeFieldType namespaces tparams (FieldType fname ftype) = do
    comment <- getTypeDescription ftype
    let pyName = Py.SingleTargetName $ encodeFieldName fname
    pyType <- annotatedExpression comment <$> encodeType namespaces tparams ftype
    return $ pyAssignmentToPyStatement $ Py.AssignmentTyped $ Py.TypedAssignment pyName pyType Nothing

encodeFunctionType :: PythonNamespaces -> TypeParams -> FunctionType -> Flow Graph Py.Expression
encodeFunctionType namespaces tparams ft = do
  pydoms <- CM.mapM encode doms
  pycod <- encode cod
  return $ pyPrimaryToPyExpression $ primaryWithSlices (pyNameToPyPrimary $ Py.Name "Callable")
    (pyPrimaryToPySlice $ Py.PrimarySimple $ Py.AtomList $
      Py.List (Py.StarNamedExpressionSimple . Py.NamedExpressionSimple <$> pydoms))
    [Py.SliceOrStarredExpressionSlice $ pyExpressionToPySlice pycod]
  where
    encode = encodeType namespaces tparams
    (doms, cod) = gatherParams [] ft
    gatherParams rdoms (FunctionType dom cod) = case stripType cod of
      TypeFunction ft2 -> gatherParams (dom:rdoms) ft2
      _ -> (L.reverse (dom:rdoms), cod)

encodeApplicationType :: PythonNamespaces -> TypeParams -> ApplicationType -> Flow Graph Py.Expression
encodeApplicationType namespaces tparams at = do
    pybody <- encodeType namespaces tparams body
    pyargs <- CM.mapM (encodeType namespaces tparams) args
    return $ primaryAndParams (pyExpressionToPyPrimary pybody) pyargs
  where
    (body, args) = gatherParams (TypeApplication at) []
    gatherParams t ps = case stripType t of
      TypeApplication (ApplicationType lhs rhs) -> gatherParams lhs (rhs:ps)
      _ -> (t, ps)

encodeLambdaType :: PythonNamespaces -> TypeParams -> LambdaType -> Flow Graph Py.Expression
encodeLambdaType namespaces tparams lt = do
    pybody <- encodeType namespaces tparams body
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

encodeName :: PythonNamespaces -> TypeParams -> Name -> Py.Name
encodeName namespaces tparams name = case M.lookup name (snd tparams) of
    Just n -> n
    Nothing -> if ns == Just focusNs
      then Py.Name local
      else Py.Name $ L.intercalate "." $ Strings.splitOn "/" $ unName name
  where
    focusNs = fst $ namespacesFocus namespaces
    QualifiedName ns local = qualifyNameEager name

encodeNamespace :: Namespace -> Py.DottedName
encodeNamespace ns = Py.DottedName (Py.Name <$> (Strings.splitOn "/" $ unNamespace ns))

encodeRecordType :: PythonNamespaces -> Name -> RowType -> TypeParams -> Maybe String -> Flow Graph Py.Statement
encodeRecordType namespaces name (RowType _ tfields) tparams comment = do
    pyFields <- CM.mapM (encodeFieldType namespaces tparams) tfields
    let body = Py.BlockIndented pyFields
    return $ Py.StatementCompound $ Py.CompoundStatementClassDef $
      Py.ClassDefinition (Just decs) (Py.Name lname) [] args comment body
  where
    lname = localNameOfEager name
    pytparams = snd <$> fst tparams
    args = if L.null pytparams
      then Nothing
      else Just $ Py.Args [Py.PosArgExpression $ pyPrimaryToPyExpression $
        primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Generic") (pyNameToPyExpression <$> pytparams)] [] []
    decs = Py.Decorators [pyNameToPyNamedExpression $ Py.Name "dataclass"]

encodeTerm :: PythonNamespaces -> Term -> Flow Graph Py.Expression
encodeTerm namespaces term = fail "not yet implemented"

encodeType :: PythonNamespaces -> TypeParams -> Type -> Flow Graph Py.Expression
encodeType namespaces tparams typ = case stripType typ of
    TypeApplication at -> encodeApplicationType namespaces tparams at
    TypeFunction ft -> encodeFunctionType namespaces tparams ft
    TypeLambda lt -> encodeLambdaType namespaces tparams lt
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
    encode = encodeType namespaces tparams
    dflt = pure $ stringToPyExpression $ "type = " ++ show (stripType typ)
    variableReference name = pure $ pyNameToPyExpression $ encodeName namespaces tparams name

encodeTypeAssignment :: PythonNamespaces -> Name -> Type -> TypeParams -> Maybe String
  -> Flow Graph ([Py.Statement], S.Set Py.Name)
encodeTypeAssignment namespaces name typ tparams@(tnames, tmap) comment = case stripType typ of
    TypeLambda (LambdaType var body) -> encodeTypeAssignment namespaces name body tparams2 comment
      where
        tparams2 = (tnames ++ [(var, pyvar)], M.insert var pyvar tmap)
          where
            pyvar = Py.Name $ capitalize $ unName var
    TypeRecord rt -> do
      st <- encodeRecordType namespaces name rt tparams comment
      return ([st], tvars)
    TypeUnion rt -> do
      st <- encodeUnionType namespaces name rt tparams comment
      return (st, tvars)
    TypeWrap (WrappedType _ t) -> singleNewtype <$> encodeType namespaces tparams t
    t -> singleTypedef <$> encodeType namespaces tparams t
  where
    single st = ([st], tvars)
    singleNewtype e = single $ newtypeStatement (Py.Name $ localNameOfEager name) comment e
    singleTypedef e = single $ typeAliasStatement (Py.Name $ localNameOfEager name) comment e
    tvars = S.fromList (snd <$> (fst tparams))

-- TODO: consider producing Python enums where appropriate
encodeUnionType :: PythonNamespaces -> Name -> RowType -> TypeParams -> Maybe String -> Flow Graph [Py.Statement]
encodeUnionType namespaces name (RowType _ tfields) tparams comment = do
    fieldStmts <- CM.mapM toFieldStmt tfields
    return $ fieldStmts ++ [unionStmt]
  where
    toFieldStmt (FieldType fname ftype) = do
        fcomment <- getTypeDescription ftype
        if isUnitType (stripType ftype)
          then pure $ assignmentStatement (variantName fname) $
            pyPrimaryToPyExpression $ primaryWithExpressionSlices (pyNameToPyPrimary $ Py.Name "Literal")
              [stringToPyExpression $ unName fname]
          else newtypeStatement (variantName fname) fcomment <$> encodeType namespaces tparams ftype
    unionStmt = typeAliasStatement ((Py.Name $ localNameOfEager name)) comment $
      orExpression (pyNameToPyPrimary . variantName . fieldTypeName <$> tfields)
    variantName fname = Py.Name $ (localNameOfEager name) ++ (capitalize $ unName fname)

moduleToPythonModule :: Module -> Flow Graph Py.Module
moduleToPythonModule mod = do
  namespaces <- namespacesForModule mod
  transformModule pythonLanguage (encodeTerm namespaces) (constructModule namespaces) mod

moduleToPython :: Module -> Flow Graph (M.Map FilePath String)
moduleToPython mod = do
  file <- moduleToPythonModule mod
  let s = printExpr $ parenthesize $ encodeModule file
  let path = namespaceToFilePath False (FileExtension "py") $ moduleNamespace mod
  return $ M.fromList [(path, s)]

namespacesForModule :: Module -> Flow Graph PythonNamespaces
namespacesForModule mod = do
    nss <- moduleDependencyNamespaces True True True True mod
    return $ Namespaces (toPair focusNs) $ M.fromList (toPair <$> S.toList nss)
  where
    focusNs = moduleNamespace mod
    toPair ns = (ns, encodeNamespace ns)

toDataDeclarations :: M.Map Type (Coder Graph Graph Term Py.Expression) -> PythonNamespaces -> (Element, TypedTerm)
  -> Flow Graph [Py.Statement]
toDataDeclarations coders namespaces (el, TypedTerm term typ) = withTrace ("data element " ++ unName (elementName el)) $ do
  comment <- getTermDescription term
  return [pySimpleStatementToPyStatement Py.SimpleStatementContinue]

toTypeDeclarations :: PythonNamespaces -> Element -> Term -> Flow Graph ([Py.Statement], S.Set Py.Name)
toTypeDeclarations namespaces el term = withTrace ("type element " ++ unName name) $ do
    typ <- coreDecodeType term >>= adaptType pythonLanguage
    comment <- getTypeDescription typ
    encodeTypeAssignment namespaces name typ ([], M.empty) comment
  where
    name = elementName el
