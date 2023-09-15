module Hydra.Langs.Java.Utils where

import Hydra.Kernel
import Hydra.Langs.Java.Language
import Hydra.Langs.Java.Names
import qualified Hydra.Langs.Java.Syntax as Java
import qualified Hydra.Lib.Strings as Strings

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


type PackageMap = M.Map Namespace Java.PackageName

data Aliases = Aliases {
  aliasesCurrentNamespace :: Namespace,
  aliasesPackages :: PackageMap,
  aliasesRecursiveVars :: S.Set Name } deriving Show

addExpressions :: [Java.MultiplicativeExpression] -> Java.AdditiveExpression
addExpressions exprs = L.foldl add (Java.AdditiveExpressionUnary $ L.head exprs) $ L.tail exprs
  where
    add ae me = Java.AdditiveExpressionPlus $ Java.AdditiveExpression_Binary ae me

addJavaTypeParameter :: Java.ReferenceType -> Java.Type -> Flow (Graph Kv) Java.Type
addJavaTypeParameter rt t = case t of
  Java.TypeReference rt1 -> case rt1 of
    Java.ReferenceTypeClassOrInterface cit -> case cit of
      Java.ClassOrInterfaceTypeClass (Java.ClassType anns qual id args) -> pure $
        Java.TypeReference $ Java.ReferenceTypeClassOrInterface $
          Java.ClassOrInterfaceTypeClass $ Java.ClassType anns qual id (args ++ [Java.TypeArgumentReference rt])
      _ -> fail $ "expected a Java class type. Found: " ++ show cit
    Java.ReferenceTypeVariable tv -> pure $ javaTypeVariableToType tv
    _ -> fail $ "expected a Java class or interface type, or a variable. Found: " ++ show rt
  _ -> fail $ "expected a reference type. Found: " ++ show t

fieldExpression :: Java.Identifier -> Java.Identifier -> Java.ExpressionName
fieldExpression varId fieldId = Java.ExpressionName (Just $ Java.AmbiguousName [varId]) fieldId

fieldNameToJavaExpression :: FieldName -> Java.Expression
fieldNameToJavaExpression fname = javaPostfixExpressionToJavaExpression $
  Java.PostfixExpressionName $ Java.ExpressionName Nothing (fieldNameToJavaIdentifier fname)

fieldNameToJavaIdentifier :: FieldName -> Java.Identifier
fieldNameToJavaIdentifier (FieldName name) = javaIdentifier name

fieldNameToJavaVariableDeclarator :: FieldName -> Java.VariableDeclarator
fieldNameToJavaVariableDeclarator (FieldName n) = javaVariableDeclarator (javaIdentifier n) Nothing

fieldNameToJavaVariableDeclaratorId :: FieldName -> Java.VariableDeclaratorId
fieldNameToJavaVariableDeclaratorId (FieldName n) = javaVariableDeclaratorId $ javaIdentifier n

importAliasesForModule :: Module Kv -> Aliases
importAliasesForModule mod = Aliases (moduleNamespace mod) M.empty S.empty

interfaceMethodDeclaration :: [Java.InterfaceMethodModifier] -> [Java.TypeParameter] -> String -> [Java.FormalParameter]
   -> Java.Result -> Maybe [Java.BlockStatement] -> Java.InterfaceMemberDeclaration
interfaceMethodDeclaration mods tparams methodName params result stmts = Java.InterfaceMemberDeclarationInterfaceMethod $
    Java.InterfaceMethodDeclaration mods header body
  where
    header = javaMethodHeader tparams methodName params result
    body = javaMethodBody stmts

isEscaped :: String -> Bool
isEscaped s = L.head s == '$'

javaAdditiveExpressionToJavaExpression :: Java.AdditiveExpression -> Java.Expression
javaAdditiveExpressionToJavaExpression = javaRelationalExpressionToJavaExpression .
  Java.RelationalExpressionSimple . Java.ShiftExpressionUnary

javaAssignmentStatement :: Java.LeftHandSide -> Java.Expression -> Java.Statement
javaAssignmentStatement lhs rhs = Java.StatementWithoutTrailing $ Java.StatementWithoutTrailingSubstatementExpression $
    Java.ExpressionStatement $ Java.StatementExpressionAssignment ass
  where
    ass = Java.Assignment lhs Java.AssignmentOperatorSimple rhs

javaBoolean :: Bool -> Java.Literal
javaBoolean = Java.LiteralBoolean

javaBooleanExpression :: Bool -> Java.Expression
javaBooleanExpression = javaPrimaryToJavaExpression . javaLiteralToJavaPrimary . javaBoolean

javaBooleanType :: Java.Type
javaBooleanType = javaPrimitiveTypeToJavaType Java.PrimitiveTypeBoolean

javaCastExpression :: Java.ReferenceType -> Java.UnaryExpression -> Java.CastExpression
javaCastExpression rt expr = Java.CastExpressionNotPlusMinus $ Java.CastExpression_NotPlusMinus rb expr
  where
    rb = Java.CastExpression_RefAndBounds rt []

javaCastExpressionToJavaExpression :: Java.CastExpression -> Java.Expression
javaCastExpressionToJavaExpression = javaUnaryExpressionToJavaExpression . Java.UnaryExpressionOther .
  Java.UnaryExpressionNotPlusMinusCast

javaClassDeclaration :: Aliases -> [Java.TypeParameter] -> Name -> [Java.ClassModifier]
   -> Maybe Name -> [Java.InterfaceType] -> [Java.ClassBodyDeclarationWithComments] -> Java.ClassDeclaration
javaClassDeclaration aliases tparams elName mods supname impls bodyDecls = Java.ClassDeclarationNormal $ Java.NormalClassDeclaration {
  Java.normalClassDeclarationModifiers = mods,
  Java.normalClassDeclarationIdentifier = javaDeclName elName,
  Java.normalClassDeclarationParameters = tparams,
  Java.normalClassDeclarationExtends = fmap (\n -> nameToJavaClassType aliases True [] n Nothing) supname,
  Java.normalClassDeclarationImplements = impls,
  Java.normalClassDeclarationBody = Java.ClassBody bodyDecls}

javaClassType :: [Java.ReferenceType] -> Maybe Java.PackageName -> String -> Java.ClassType
javaClassType args pkg id = Java.ClassType [] qual (javaTypeIdentifier id) targs
  where
    qual = maybe Java.ClassTypeQualifierNone Java.ClassTypeQualifierPackage pkg
    targs = Java.TypeArgumentReference <$> args

javaClassTypeToJavaType :: Java.ClassType -> Java.Type
javaClassTypeToJavaType = Java.TypeReference . Java.ReferenceTypeClassOrInterface . Java.ClassOrInterfaceTypeClass

javaConditionalAndExpressionToJavaExpression :: Java.ConditionalAndExpression -> Java.Expression
javaConditionalAndExpressionToJavaExpression condAndEx = Java.ExpressionAssignment $
  Java.AssignmentExpressionConditional $ Java.ConditionalExpressionSimple $ Java.ConditionalOrExpression [condAndEx]

javaConstructorCall :: Java.ClassOrInterfaceTypeToInstantiate -> [Java.Expression] -> Maybe Java.ClassBody -> Java.Expression
javaConstructorCall ci args mbody = javaPrimaryToJavaExpression $
  Java.PrimaryNoNewArray $
  Java.PrimaryNoNewArrayClassInstance $
  Java.ClassInstanceCreationExpression Nothing $
  Java.UnqualifiedClassInstanceCreationExpression [] ci args mbody

javaConstructorName :: Java.Identifier -> Maybe Java.TypeArgumentsOrDiamond -> Java.ClassOrInterfaceTypeToInstantiate
javaConstructorName id targs = Java.ClassOrInterfaceTypeToInstantiate [Java.AnnotatedIdentifier [] id] targs

javaDeclName :: Name -> Java.TypeIdentifier
javaDeclName = Java.TypeIdentifier . javaVariableName

javaEmptyStatement :: Java.Statement
javaEmptyStatement = Java.StatementWithoutTrailing $ Java.StatementWithoutTrailingSubstatementEmpty Java.EmptyStatement

javaEqualityExpressionToJavaInclusiveOrExpression :: Java.EqualityExpression -> Java.InclusiveOrExpression
javaEqualityExpressionToJavaInclusiveOrExpression eq = Java.InclusiveOrExpression [
  Java.ExclusiveOrExpression [Java.AndExpression [eq]]]

javaExpressionNameToJavaExpression :: Java.ExpressionName -> Java.Expression
javaExpressionNameToJavaExpression = javaPostfixExpressionToJavaExpression . Java.PostfixExpressionName

javaExpressionToJavaPrimary :: Java.Expression -> Java.Primary
javaExpressionToJavaPrimary = Java.PrimaryNoNewArray . Java.PrimaryNoNewArrayParens

javaExpressionToJavaUnaryExpression :: Java.Expression -> Java.UnaryExpression
javaExpressionToJavaUnaryExpression = javaPrimaryToJavaUnaryExpression . javaExpressionToJavaPrimary

javaFieldAccessToJavaExpression :: Java.FieldAccess -> Java.Expression
javaFieldAccessToJavaExpression = javaPrimaryToJavaExpression . Java.PrimaryNoNewArray . Java.PrimaryNoNewArrayFieldAccess

javaIdentifier :: String -> Java.Identifier
javaIdentifier = Java.Identifier . sanitizeJavaName

javaIdentifierToJavaExpressionName :: Java.Identifier -> Java.ExpressionName
javaIdentifierToJavaExpressionName id = Java.ExpressionName Nothing id

javaIdentifierToJavaExpression :: Java.Identifier -> Java.Expression
javaIdentifierToJavaExpression = javaUnaryExpressionToJavaExpression . javaIdentifierToJavaUnaryExpression

javaIdentifierToJavaRelationalExpression :: Java.Identifier -> Java.RelationalExpression
javaIdentifierToJavaRelationalExpression id = javaPostfixExpressionToJavaRelationalExpression $
  Java.PostfixExpressionName $ Java.ExpressionName Nothing id

javaIdentifierToJavaUnaryExpression :: Java.Identifier -> Java.UnaryExpression
javaIdentifierToJavaUnaryExpression = javaRelationalExpressionToJavaUnaryExpression . javaIdentifierToJavaRelationalExpression

javaInstanceOf :: Java.RelationalExpression -> Java.ReferenceType -> Java.RelationalExpression
javaInstanceOf lhs rhs = Java.RelationalExpressionInstanceof $ Java.RelationalExpression_InstanceOf lhs rhs

javaInt :: Integral a => a -> Java.Literal
javaInt i = Java.LiteralInteger $ Java.IntegerLiteral $ fromIntegral i

javaIntExpression :: Integer -> Java.Expression
javaIntExpression = javaPrimaryToJavaExpression . javaLiteralToJavaPrimary . javaInt

javaIntType :: Java.Type
javaIntType = javaPrimitiveTypeToJavaType $ Java.PrimitiveTypeNumeric $ Java.NumericTypeIntegral Java.IntegralTypeInt

javaInterfaceDeclarationToJavaClassBodyDeclaration :: Java.NormalInterfaceDeclaration -> Java.ClassBodyDeclaration
javaInterfaceDeclarationToJavaClassBodyDeclaration = Java.ClassBodyDeclarationClassMember .
  Java.ClassMemberDeclarationInterface . Java.InterfaceDeclarationNormalInterface

javaLambda :: Name -> Java.Expression -> Java.Expression
javaLambda var jbody = Java.ExpressionLambda $ Java.LambdaExpression params (Java.LambdaBodyExpression jbody)
  where
    params = Java.LambdaParametersSingle $ variableToJavaIdentifier var

javaLambdaFromBlock :: Name -> Java.Block -> Java.Expression
javaLambdaFromBlock var block = Java.ExpressionLambda $ Java.LambdaExpression params (Java.LambdaBodyBlock block)
  where
    params = Java.LambdaParametersSingle $ variableToJavaIdentifier var

javaLiteralToJavaExpression = javaRelationalExpressionToJavaExpression .
  javaMultiplicativeExpressionToJavaRelationalExpression .
  javaLiteralToJavaMultiplicativeExpression

javaLiteralToJavaMultiplicativeExpression = Java.MultiplicativeExpressionUnary . javaPrimaryToJavaUnaryExpression .
  javaLiteralToJavaPrimary

javaLiteralToJavaPrimary :: Java.Literal -> Java.Primary
javaLiteralToJavaPrimary = Java.PrimaryNoNewArray . Java.PrimaryNoNewArrayLiteral

javaMemberField :: [Java.FieldModifier] -> Java.Type -> Java.VariableDeclarator -> Java.ClassBodyDeclaration
javaMemberField mods jt var = Java.ClassBodyDeclarationClassMember $ Java.ClassMemberDeclarationField $
  Java.FieldDeclaration mods (Java.UnannType jt) [var]

javaMethodBody :: Maybe [Java.BlockStatement] -> Java.MethodBody
javaMethodBody stmts = Y.maybe Java.MethodBodyNone (Java.MethodBodyBlock . Java.Block) stmts

javaMethodDeclarationToJavaClassBodyDeclaration :: Java.MethodDeclaration -> Java.ClassBodyDeclaration
javaMethodDeclarationToJavaClassBodyDeclaration = Java.ClassBodyDeclarationClassMember . Java.ClassMemberDeclarationMethod

javaMethodHeader :: [Java.TypeParameter] -> String -> [Java.FormalParameter] -> Java.Result -> Java.MethodHeader
javaMethodHeader tparams methodName params result = Java.MethodHeader tparams result decl mthrows
  where
    decl = Java.MethodDeclarator (Java.Identifier methodName) Nothing params
    mthrows = Nothing

javaMethodInvocationToJavaExpression :: Java.MethodInvocation -> Java.Expression
javaMethodInvocationToJavaExpression = javaPrimaryToJavaExpression . javaMethodInvocationToJavaPrimary

javaMethodInvocationToJavaStatement :: Java.MethodInvocation -> Java.Statement
javaMethodInvocationToJavaStatement = Java.StatementWithoutTrailing . Java.StatementWithoutTrailingSubstatementExpression .
  Java.ExpressionStatement . Java.StatementExpressionMethodInvocation

javaMethodInvocationToJavaPostfixExpression :: Java.MethodInvocation -> Java.PostfixExpression
javaMethodInvocationToJavaPostfixExpression = Java.PostfixExpressionPrimary . Java.PrimaryNoNewArray .
  Java.PrimaryNoNewArrayMethodInvocation

javaMethodInvocationToJavaPrimary :: Java.MethodInvocation -> Java.Primary
javaMethodInvocationToJavaPrimary = Java.PrimaryNoNewArray .
  Java.PrimaryNoNewArrayMethodInvocation

javaMultiplicativeExpressionToJavaRelationalExpression :: Java.MultiplicativeExpression -> Java.RelationalExpression
javaMultiplicativeExpressionToJavaRelationalExpression = Java.RelationalExpressionSimple .
  Java.ShiftExpressionUnary . Java.AdditiveExpressionUnary

javaPackageDeclaration :: Namespace -> Java.PackageDeclaration
javaPackageDeclaration (Namespace name) = Java.PackageDeclaration [] (Java.Identifier <$> Strings.splitOn "/" name)

javaPostfixExpressionToJavaEqualityExpression :: Java.PostfixExpression -> Java.EqualityExpression
javaPostfixExpressionToJavaEqualityExpression = Java.EqualityExpressionUnary .
  javaUnaryExpressionToJavaRelationalExpression . Java.UnaryExpressionOther . Java.UnaryExpressionNotPlusMinusPostfix

javaPostfixExpressionToJavaExpression :: Java.PostfixExpression -> Java.Expression
javaPostfixExpressionToJavaExpression = javaRelationalExpressionToJavaExpression .
  javaPostfixExpressionToJavaRelationalExpression

javaPostfixExpressionToJavaInclusiveOrExpression :: Java.PostfixExpression -> Java.InclusiveOrExpression
javaPostfixExpressionToJavaInclusiveOrExpression = javaEqualityExpressionToJavaInclusiveOrExpression .
  javaPostfixExpressionToJavaEqualityExpression

javaPostfixExpressionToJavaRelationalExpression :: Java.PostfixExpression -> Java.RelationalExpression
javaPostfixExpressionToJavaRelationalExpression =
  javaUnaryExpressionToJavaRelationalExpression . javaPostfixExpressionToJavaUnaryExpression

javaPostfixExpressionToJavaUnaryExpression :: Java.PostfixExpression -> Java.UnaryExpression
javaPostfixExpressionToJavaUnaryExpression = Java.UnaryExpressionOther . Java.UnaryExpressionNotPlusMinusPostfix

javaPrimaryToJavaExpression :: Java.Primary -> Java.Expression
javaPrimaryToJavaExpression = javaPostfixExpressionToJavaExpression . Java.PostfixExpressionPrimary

javaPrimaryToJavaUnaryExpression :: Java.Primary -> Java.UnaryExpression
javaPrimaryToJavaUnaryExpression = Java.UnaryExpressionOther .
  Java.UnaryExpressionNotPlusMinusPostfix .
  Java.PostfixExpressionPrimary

javaPrimitiveTypeToJavaType :: Java.PrimitiveType -> Java.Type
javaPrimitiveTypeToJavaType pt = Java.TypePrimitive $ Java.PrimitiveTypeWithAnnotations pt []

javaRefType :: [Java.ReferenceType] -> Maybe Java.PackageName -> String -> Java.Type
javaRefType args pkg id = Java.TypeReference $ Java.ReferenceTypeClassOrInterface $ Java.ClassOrInterfaceTypeClass $
  javaClassType args pkg id

javaRelationalExpressionToJavaExpression :: Java.RelationalExpression -> Java.Expression
javaRelationalExpressionToJavaExpression relEx = javaConditionalAndExpressionToJavaExpression $
    Java.ConditionalAndExpression [javaEqualityExpressionToJavaInclusiveOrExpression $ Java.EqualityExpressionUnary relEx]

javaRelationalExpressionToJavaUnaryExpression :: Java.RelationalExpression -> Java.UnaryExpression
javaRelationalExpressionToJavaUnaryExpression = javaPrimaryToJavaUnaryExpression .
  Java.PrimaryNoNewArray .
  Java.PrimaryNoNewArrayParens .
  javaRelationalExpressionToJavaExpression

javaReturnStatement :: Y.Maybe Java.Expression -> Java.Statement
javaReturnStatement mex = Java.StatementWithoutTrailing $ Java.StatementWithoutTrailingSubstatementReturn $
  Java.ReturnStatement mex

javaStatementsToBlock :: [Java.Statement] -> Java.Block
javaStatementsToBlock stmts = Java.Block (Java.BlockStatementStatement <$> stmts)

javaString :: String -> Java.Literal
javaString = Java.LiteralString . Java.StringLiteral

javaStringMultiplicativeExpression :: String -> Java.MultiplicativeExpression
javaStringMultiplicativeExpression = javaLiteralToJavaMultiplicativeExpression . javaString

javaThis :: Java.Expression
javaThis = javaPrimaryToJavaExpression $ Java.PrimaryNoNewArray Java.PrimaryNoNewArrayThis

javaTypeFromTypeName :: Aliases -> Name -> Java.Type
javaTypeFromTypeName aliases elName = javaTypeVariableToType $ Java.TypeVariable [] $
  nameToJavaTypeIdentifier aliases False elName

javaTypeIdentifier :: String -> Java.TypeIdentifier
javaTypeIdentifier = Java.TypeIdentifier . Java.Identifier

javaTypeIdentifierToJavaTypeArgument :: Java.TypeIdentifier -> Java.TypeArgument
javaTypeIdentifierToJavaTypeArgument id = Java.TypeArgumentReference $ Java.ReferenceTypeVariable $ Java.TypeVariable [] id

javaTypeName :: Java.Identifier -> Java.TypeName
javaTypeName id = Java.TypeName (Java.TypeIdentifier id) Nothing

javaTypeParameter :: String -> Java.TypeParameter
javaTypeParameter v = Java.TypeParameter [] (javaTypeIdentifier v) Nothing

javaTypeToJavaFormalParameter :: Java.Type -> FieldName -> Java.FormalParameter
javaTypeToJavaFormalParameter jt fname = Java.FormalParameterSimple $ Java.FormalParameter_Simple [] argType argId
  where
    argType = Java.UnannType jt
    argId = fieldNameToJavaVariableDeclaratorId fname

javaTypeToJavaReferenceType :: Java.Type -> Flow (Graph Kv) Java.ReferenceType
javaTypeToJavaReferenceType t = case t of
  Java.TypeReference rt -> pure rt
  _ -> fail $ "expected a Java reference type. Found: " ++ show t

javaTypeToJavaResult :: Java.Type -> Java.Result
javaTypeToJavaResult = Java.ResultType . Java.UnannType

javaTypeToJavaTypeArgument :: Java.Type -> Java.TypeArgument
javaTypeToJavaTypeArgument t = case t of
  Java.TypeReference rt -> Java.TypeArgumentReference rt
  _ -> Java.TypeArgumentWildcard $ Java.Wildcard [] Nothing -- TODO

javaTypeVariable :: String -> Java.ReferenceType
javaTypeVariable v = Java.ReferenceTypeVariable $ Java.TypeVariable [] $ javaTypeIdentifier $ capitalize v

javaTypeVariableToType :: Java.TypeVariable -> Java.Type
javaTypeVariableToType = Java.TypeReference . Java.ReferenceTypeVariable

javaUnaryExpressionToJavaExpression :: Java.UnaryExpression -> Java.Expression
javaUnaryExpressionToJavaExpression = javaRelationalExpressionToJavaExpression .
  javaUnaryExpressionToJavaRelationalExpression

javaUnaryExpressionToJavaRelationalExpression :: Java.UnaryExpression -> Java.RelationalExpression
javaUnaryExpressionToJavaRelationalExpression = javaMultiplicativeExpressionToJavaRelationalExpression .
  Java.MultiplicativeExpressionUnary

javaVariableDeclarator :: Java.Identifier -> Y.Maybe Java.VariableInitializer -> Java.VariableDeclarator
javaVariableDeclarator id = Java.VariableDeclarator (javaVariableDeclaratorId id)

javaVariableDeclaratorId :: Java.Identifier -> Java.VariableDeclaratorId
javaVariableDeclaratorId id = Java.VariableDeclaratorId id Nothing

javaVariableName :: Name -> Java.Identifier
javaVariableName = javaIdentifier . localNameOfEager

makeConstructor :: Aliases -> Name -> Bool -> [Java.FormalParameter]
  -> [Java.BlockStatement] -> Java.ClassBodyDeclaration
makeConstructor aliases elName private params stmts = Java.ClassBodyDeclarationConstructorDeclaration $
    Java.ConstructorDeclaration mods cons Nothing body
  where
    nm = Java.SimpleTypeName $ nameToJavaTypeIdentifier aliases False elName
    cons = Java.ConstructorDeclarator [] nm Nothing params
    mods = [if private then Java.ConstructorModifierPrivate else Java.ConstructorModifierPublic]
    body = Java.ConstructorBody Nothing stmts

methodDeclaration :: [Java.MethodModifier] -> [Java.TypeParameter] -> [Java.Annotation] -> String
  -> [Java.FormalParameter] -> Java.Result -> Maybe [Java.BlockStatement] -> Java.ClassBodyDeclaration
methodDeclaration mods tparams anns methodName params result stmts =
    javaMethodDeclarationToJavaClassBodyDeclaration $
    Java.MethodDeclaration anns mods header body
  where
    header = javaMethodHeader tparams methodName params result
    body = javaMethodBody stmts

methodInvocation :: Y.Maybe (Either Java.ExpressionName Java.Primary) -> Java.Identifier -> [Java.Expression] -> Java.MethodInvocation
methodInvocation lhs methodName = Java.MethodInvocation header
  where
    header = case lhs of
      Nothing -> Java.MethodInvocation_HeaderSimple $ Java.MethodName methodName
      Just either -> Java.MethodInvocation_HeaderComplex $ Java.MethodInvocation_Complex variant targs methodName
        where
          targs = []
          variant = case either of
            Left name -> Java.MethodInvocation_VariantExpression name
            Right prim -> Java.MethodInvocation_VariantPrimary prim

methodInvocationStatic :: Java.Identifier -> Java.Identifier -> [Java.Expression] -> Java.MethodInvocation
methodInvocationStatic self methodName = methodInvocation (Just $ Left name) methodName
  where
    name = Java.ExpressionName Nothing self

nameToJavaClassType :: Aliases -> Bool -> [Java.TypeArgument] -> Name -> Maybe String -> Java.ClassType
nameToJavaClassType aliases qualify args name mlocal = Java.ClassType [] pkg id args
  where
    (id, pkg) = nameToQualifiedJavaName aliases qualify name mlocal

nameToQualifiedJavaName :: Aliases -> Bool -> Name -> Maybe String -> (Java.TypeIdentifier, Java.ClassTypeQualifier)
nameToQualifiedJavaName aliases qualify name mlocal = (jid, pkg)
  where
    QualifiedName ns local = qualifyNameEager name
    alias = case ns of
      Nothing -> Nothing
      Just n -> case M.lookup n (aliasesPackages aliases) of
          Nothing -> Just $ javaPackageName $ Strings.splitOn "/" $ unNamespace n
          Just id -> Just id
    pkg = if qualify
      then Y.maybe none Java.ClassTypeQualifierPackage alias
      else none
    none = Java.ClassTypeQualifierNone
    jid = javaTypeIdentifier $ case mlocal of
      Nothing -> sanitizeJavaName local
      Just l -> sanitizeJavaName local ++ "." ++ sanitizeJavaName l

nameToJavaName :: Aliases -> Name -> Java.Identifier
nameToJavaName aliases name = Java.Identifier $ if isEscaped (unName name)
    then sanitizeJavaName local
    else case ns of
      Nothing -> local
      Just gname -> case M.lookup gname (aliasesPackages aliases) of
        Nothing -> fromParts $ Strings.splitOn "/" $ unNamespace gname
        Just (Java.PackageName parts) -> fromParts (Java.unIdentifier <$> parts)
  where
    QualifiedName ns local = qualifyNameEager name
    fromParts parts = L.intercalate "." $ parts ++ [sanitizeJavaName local]

nameToJavaReferenceType :: Aliases -> Bool -> [Java.TypeArgument] -> Name -> Maybe String -> Java.ReferenceType
nameToJavaReferenceType aliases qualify args name mlocal = Java.ReferenceTypeClassOrInterface $ Java.ClassOrInterfaceTypeClass $
  nameToJavaClassType aliases qualify args name mlocal

nameToJavaTypeIdentifier :: Aliases -> Bool -> Name -> Java.TypeIdentifier
nameToJavaTypeIdentifier aliases qualify name = fst $ nameToQualifiedJavaName aliases qualify name Nothing

overrideAnnotation :: Java.Annotation
overrideAnnotation = Java.AnnotationMarker $ Java.MarkerAnnotation $ javaTypeName $ Java.Identifier "Override"

referenceTypeToResult :: Java.ReferenceType -> Java.Result
referenceTypeToResult = javaTypeToJavaResult . Java.TypeReference

sanitizeJavaName :: String -> String
sanitizeJavaName name = if isEscaped name
  -- The '$' prefix allows names to be excluded from sanitization
  then unescape name
  else sanitizeWithUnderscores reservedWords name

toAcceptMethod :: Bool -> [Java.TypeParameter] -> Java.ClassBodyDeclaration
toAcceptMethod abstract vtparams = methodDeclaration mods tparams anns acceptMethodName [param] result body
  where
    mods = [Java.MethodModifierPublic] ++ if abstract then [Java.MethodModifierAbstract] else []
    tparams = [javaTypeParameter visitorReturnParameter]
    anns = if abstract
      then []
      else [overrideAnnotation]
    param = javaTypeToJavaFormalParameter ref (FieldName varName)
      where
        ref = javaClassTypeToJavaType $
          Java.ClassType
            []
            Java.ClassTypeQualifierNone
            (javaTypeIdentifier visitorName)
            (typeArgs ++ [Java.TypeArgumentReference visitorTypeVariable])
    typeArgs = (Java.TypeArgumentReference . typeParameterToReferenceType) <$> vtparams
    result = javaTypeToJavaResult $ Java.TypeReference visitorTypeVariable
    varName = "visitor"
    body = if abstract
      then Nothing
      else Just [Java.BlockStatementStatement $ javaReturnStatement $ Just returnExpr]
    returnExpr = javaMethodInvocationToJavaExpression $
        methodInvocationStatic (Java.Identifier varName) (Java.Identifier visitMethodName) [javaThis]

toAssignStmt :: FieldName -> Java.Statement
toAssignStmt fname = javaAssignmentStatement lhs rhs
  where
    lhs = Java.LeftHandSideFieldAccess $ thisField id
      where
        id = fieldNameToJavaIdentifier fname
    rhs = fieldNameToJavaExpression fname
    thisField = Java.FieldAccess $ Java.FieldAccess_QualifierPrimary $ Java.PrimaryNoNewArray Java.PrimaryNoNewArrayThis

toJavaArrayType :: Java.Type -> Flow (Graph Kv) Java.Type
toJavaArrayType t = Java.TypeReference . Java.ReferenceTypeArray <$> case t of
  Java.TypeReference rt -> case rt of
    Java.ReferenceTypeClassOrInterface cit -> pure $
      Java.ArrayType (Java.Dims [[]]) $ Java.ArrayType_VariantClassOrInterface cit
    Java.ReferenceTypeArray (Java.ArrayType (Java.Dims d) v) -> pure $
      Java.ArrayType (Java.Dims $ d ++ [[]]) v
    _ -> fail $ "don't know how to make Java reference type into array type: " ++ show rt
  _ -> fail $ "don't know how to make Java type into array type: " ++ show t

typeParameterToTypeArgument :: Java.TypeParameter -> Java.TypeArgument
typeParameterToTypeArgument (Java.TypeParameter _ id _) = javaTypeIdentifierToJavaTypeArgument id

typeParameterToReferenceType :: Java.TypeParameter -> Java.ReferenceType
typeParameterToReferenceType = javaTypeVariable . unTypeParameter

unTypeParameter :: Java.TypeParameter -> String
unTypeParameter (Java.TypeParameter [] (Java.TypeIdentifier (Java.Identifier v)) Nothing) = v

unescape :: String -> String
unescape = L.tail

variableDeclarationStatement :: Aliases -> Java.Type -> Java.Identifier -> Java.Expression -> Java.BlockStatement
variableDeclarationStatement aliases jtype id rhs = Java.BlockStatementLocalVariableDeclaration $
    Java.LocalVariableDeclarationStatement $ Java.LocalVariableDeclaration [] (Java.LocalVariableTypeType $ Java.UnannType jtype) [vdec]
  where
    vdec = javaVariableDeclarator id (Just init)
      where
        init = Java.VariableInitializerExpression rhs

variableToJavaIdentifier :: Name -> Java.Identifier
variableToJavaIdentifier (Name var) = Java.Identifier $ if var == ignoredVariable
  then "ignored"
  else var -- TODO: escape

variantClassName :: Bool -> Name -> FieldName -> Name
variantClassName qualify elName (FieldName fname) = unqualifyName (QualifiedName ns local1)
  where
    QualifiedName ns local = qualifyNameEager elName
    flocal = capitalize fname
    local1 = if qualify
      then local ++ "." ++ flocal
      else if flocal == local then flocal ++ "_" else flocal

visitorTypeVariable :: Java.ReferenceType
visitorTypeVariable = javaTypeVariable "r"
