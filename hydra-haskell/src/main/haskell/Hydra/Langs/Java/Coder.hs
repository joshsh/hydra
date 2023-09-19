module Hydra.Langs.Java.Coder (
  JavaFeatures(..),
  java8Features,
  moduleToJava,
) where

import Hydra.Kernel
import Hydra.Reduction
import Hydra.Langs.Java.Utils
import Hydra.Langs.Java.Language
import Hydra.Langs.Java.Names
import Hydra.Adapters
import Hydra.Tools.Serialization
import Hydra.Langs.Java.Serde
import Hydra.Langs.Java.Settings
import Hydra.AdapterUtils
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types
import qualified Hydra.Langs.Java.Syntax as Java

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.List.Split as LS
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y
import Data.String (String)


data JavaSymbolClass = JavaSymbolClassConstant | JavaSymbolClassNullaryFunction | JavaSymbolClassUnaryFunction | JavaSymbolLocalVariable

data JavaFeatures = JavaFeatures {
  supportsDiamondOperator :: Bool
}

java8Features = JavaFeatures {
  supportsDiamondOperator = False
}

-- For now, the supported features are hard-coded to those of Java 8, rather than being configurable.
javaFeatures = java8Features

moduleToJava :: Module -> Flow Graph (M.Map FilePath String)
moduleToJava mod = withTrace "encode module in Java" $ do
    units <- moduleToJavaCompilationUnit mod
    return $ M.fromList $ forPair <$> M.toList units
  where
    forPair (name, unit) = (elementNameToFilePath name, printExpr $ parenthesize $ writeCompilationUnit unit)

adaptTypeToJavaAndEncode :: Aliases -> Type -> Flow Graph Java.Type
adaptTypeToJavaAndEncode aliases = adaptAndEncodeType javaLanguage (encodeType aliases)

addComment :: Java.ClassBodyDeclaration -> FieldType -> Flow Graph Java.ClassBodyDeclarationWithComments
addComment decl field = Java.ClassBodyDeclarationWithComments decl <$> commentsFromFieldType field

boundTypeVariables :: Type -> [Name]
boundTypeVariables typ = case typ of
  TypeAnnotated (Annotated typ1 _) -> boundTypeVariables typ1
  TypeLambda (LambdaType v body) -> v:(boundTypeVariables body)
  _ -> []

classModsPublic :: [Java.ClassModifier]
classModsPublic = [Java.ClassModifierPublic]

classifyDataReference :: Name -> Flow Graph JavaSymbolClass
classifyDataReference name = do
  mel <- dereferenceElement name
  case mel of
    Nothing -> return JavaSymbolLocalVariable
    Just el -> do
      typ <- requireElementType el
      return $ classifyDataTerm typ $ elementData el

classifyDataTerm :: Type -> Term -> JavaSymbolClass
classifyDataTerm typ term = if isLambda term
    then JavaSymbolClassUnaryFunction
    else if hasTypeParameters || isUnsupportedVariant
      then JavaSymbolClassNullaryFunction
      else JavaSymbolClassConstant
  where
    hasTypeParameters = not $ S.null $ freeVariablesInType typ
    isUnsupportedVariant = case stripTerm term of
      TermLet _ -> True
      _ -> False

commentsFromElement :: Element -> Flow Graph (Maybe String)
commentsFromElement el = annotationClassTermDescription kvAnnotationClass (elementData el)

commentsFromFieldType :: FieldType -> Flow Graph (Maybe String)
commentsFromFieldType (FieldType _ t) = annotationClassTypeDescription kvAnnotationClass t

constructElementsInterface :: Module -> [Java.InterfaceMemberDeclaration] -> (Name, Java.CompilationUnit)
constructElementsInterface mod members = (elName, cu)
  where
    cu = Java.CompilationUnitOrdinary $ Java.OrdinaryCompilationUnit (Just pkg) [] [decl]
    pkg = javaPackageDeclaration $ moduleNamespace mod
    mods = [Java.InterfaceModifierPublic]
    className = elementsClassName $ moduleNamespace mod
    elName = unqualifyName $ QualifiedName (Just $ moduleNamespace mod) className
    body = Java.InterfaceBody members
    itf = Java.TypeDeclarationInterface $ Java.InterfaceDeclarationNormalInterface $
      Java.NormalInterfaceDeclaration mods (javaTypeIdentifier className) [] [] body
    decl = Java.TypeDeclarationWithComments itf $ moduleDescription mod

constructModule :: Module
  -> M.Map Type (Coder Graph Graph Term Java.Expression)
  -> [(Element, TypedTerm)]
  -> Flow Graph (M.Map Name Java.CompilationUnit)
constructModule mod coders pairs = do
    let isTypePair = isType . typedTermType . snd
    let typePairs = L.filter isTypePair pairs
    let dataPairs = L.filter (not . isTypePair) pairs
    typeUnits <- CM.mapM typeToClass typePairs
    dataMembers <- CM.mapM (termToInterfaceMember coders) dataPairs
    return $ M.fromList $ typeUnits ++ ([constructElementsInterface mod dataMembers | not (L.null dataMembers)])
  where
    pkg = javaPackageDeclaration $ moduleNamespace mod
    aliases = importAliasesForModule mod

    typeToClass pair@(el, _) = do
      isSer <- isSerializable el
      let imports = if isSer
                    then [Java.ImportDeclarationSingleType $ Java.SingleTypeImportDeclaration $ javaTypeName $ Java.Identifier "java.io.Serializable"]
                    else []
      decl <- declarationForType isSer aliases pair
      return (elementName el,
        Java.CompilationUnitOrdinary $ Java.OrdinaryCompilationUnit (Just pkg) imports [decl])

    -- Lambdas cannot (in general) be turned into top-level constants, as there is no way of declaring type parameters for constants
    -- These functions must be capable of handling various combinations of let and lambda terms:
    -- * Plain lambdas such as \x y -> x + y + 42
    -- * Lambdas with nested let terms, such as \x y -> let z = x + y in z + 42
    -- * Let terms with nested lambdas, such as let z = 42 in \x y -> x + y + z
    termToInterfaceMember coders pair = withTrace ("element " ++ unName (elementName el)) $ do
        expanded <- contractTerm . unshadowVariables <$> (expandLambdas (typedTermTerm $ snd pair) >>= wrapLambdas)
        case classifyDataTerm typ expanded of
          JavaSymbolClassConstant -> termToConstant coders el expanded
          JavaSymbolClassNullaryFunction -> termToNullaryMethod coders el expanded
          JavaSymbolClassUnaryFunction -> termToUnaryMethod coders el expanded
      where
        el = fst pair
        typ = typedTermType $ snd pair
        tparams = javaTypeParametersForType typ
        mname = sanitizeJavaName $ decapitalize $ localNameOfEager $ elementName el

        termToConstant coders el term = do
          jtype <- Java.UnannType <$> adaptTypeToJavaAndEncode aliases typ
          jterm <- coderEncode (Y.fromJust $ M.lookup typ coders) term
          let mods = []
          let var = javaVariableDeclarator (javaVariableName $ elementName el) $ Just $ Java.VariableInitializerExpression jterm
          return $ Java.InterfaceMemberDeclarationConstant $ Java.ConstantDeclaration mods jtype [var]

        termToNullaryMethod coders el term0 = maybeLet aliases term0 forInnerTerm
          where
            forInnerTerm aliases2 term stmts = do
              result <- javaTypeToJavaResult <$> adaptTypeToJavaAndEncode aliases2 typ
              jbody <- encodeTerm aliases2 term
              let mods = [Java.InterfaceMethodModifierStatic]
              let returnSt = Java.BlockStatementStatement $ javaReturnStatement $ Just jbody
              return $ interfaceMethodDeclaration mods tparams mname [] result (Just $ stmts ++ [returnSt])

        termToUnaryMethod coders el term = case stripType typ of
          TypeFunction (FunctionType dom cod) -> maybeLet aliases term $ \aliases2 term2 stmts2 -> case stripTerm term2 of
            TermFunction (FunctionLambda (Lambda v body)) -> do
              jdom <- adaptTypeToJavaAndEncode aliases2 dom
              jcod <- adaptTypeToJavaAndEncode aliases2 cod
              let mods = [Java.InterfaceMethodModifierStatic]
              let param = javaTypeToJavaFormalParameter jdom (FieldName $ unName v)
              let result = javaTypeToJavaResult jcod
              maybeLet aliases2 body $ \aliases3 term3 stmts3 -> do
                jbody <- encodeTerm aliases3 term3
                -- TODO: use coders
                --jbody <- coderEncode (Y.fromJust $ M.lookup typ coders) body
                let returnSt = Java.BlockStatementStatement $ javaReturnStatement $ Just jbody
                return $ interfaceMethodDeclaration mods tparams mname [param] result (Just $ stmts2 ++ stmts3 ++ [returnSt])
            _ -> unexpected "function term" $ show term
          _ -> unexpected "function type" $ show typ

declarationForLambdaType :: Bool -> Aliases
  -> [Java.TypeParameter] -> Name -> LambdaType -> Flow Graph Java.ClassDeclaration
declarationForLambdaType isSer aliases tparams elName (LambdaType (Name v) body) =
    toClassDecl False isSer aliases (tparams ++ [param]) elName body
  where
    param = javaTypeParameter $ capitalize v

declarationForRecordType :: Bool -> Bool -> Aliases -> [Java.TypeParameter] -> Name
  -> [FieldType] -> Flow Graph Java.ClassDeclaration
declarationForRecordType isInner isSer aliases tparams elName fields = do
    memberVars <- CM.mapM toMemberVar fields
    memberVars' <- CM.zipWithM addComment memberVars fields
    withMethods <- if L.length fields > 1
      then CM.mapM toWithMethod fields
      else pure []
    cons <- constructor
    tn <- if isInner then pure [] else do
      d <- typeNameDecl aliases elName
      return [d]
    let bodyDecls = tn ++ memberVars' ++ (noComment <$> [cons, equalsMethod, hashCodeMethod] ++ withMethods)
    return $ javaClassDeclaration aliases tparams elName classModsPublic Nothing (interfaceTypes isSer) bodyDecls
  where
    constructor = do
      params <- CM.mapM (fieldTypeToFormalParam aliases) fields
      let stmts = Java.BlockStatementStatement . toAssignStmt . fieldTypeName <$> fields
      return $ makeConstructor aliases elName False params stmts

    fieldArgs = fieldNameToJavaExpression . fieldTypeName <$> fields

    toMemberVar (FieldType fname ft) = do
      let mods = [Java.FieldModifierPublic, Java.FieldModifierFinal]
      jt <- adaptTypeToJavaAndEncode aliases ft
      let var = fieldNameToJavaVariableDeclarator fname
      return $ javaMemberField mods jt var

    toWithMethod field = do
      let mods = [Java.MethodModifierPublic]
      let methodName = "with" ++ capitalize (unFieldName $ fieldTypeName field)
      param <- fieldTypeToFormalParam aliases field
      let anns = [] -- TODO
      let result = referenceTypeToResult $ nameToJavaReferenceType aliases False [] elName Nothing
      let consId = Java.Identifier $ sanitizeJavaName $ localNameOfEager elName
      let returnStmt = Java.BlockStatementStatement $ javaReturnStatement $ Just $
            javaConstructorCall (javaConstructorName consId Nothing) fieldArgs Nothing
      return $ methodDeclaration mods [] anns methodName [param] result (Just [returnStmt])

    equalsMethod = methodDeclaration mods [] anns equalsMethodName [param] result $
        Just [instanceOfStmt,
          castStmt,
          returnAllFieldsEqual]
      where
        anns = [overrideAnnotation]
        mods = [Java.MethodModifierPublic]
        param = javaTypeToJavaFormalParameter (javaRefType [] Nothing "Object") (FieldName otherInstanceName)
        result = javaTypeToJavaResult javaBooleanType
        tmpName = "o"

        instanceOfStmt = Java.BlockStatementStatement $ Java.StatementIfThen $
            Java.IfThenStatement cond returnFalse
          where
            cond = javaUnaryExpressionToJavaExpression $
                Java.UnaryExpressionOther $
                Java.UnaryExpressionNotPlusMinusNot $
                javaRelationalExpressionToJavaUnaryExpression $
                javaInstanceOf other parent
              where
                other = javaIdentifierToJavaRelationalExpression $ javaIdentifier otherInstanceName
                parent = nameToJavaReferenceType aliases False [] elName Nothing

            returnFalse = javaReturnStatement $ Just $ javaBooleanExpression False

        castStmt = variableDeclarationStatement aliases jtype id rhs
          where
            jtype = javaTypeFromTypeName aliases elName
            id = javaIdentifier tmpName
            rhs = javaCastExpressionToJavaExpression $ javaCastExpression rt var
            var = javaIdentifierToJavaUnaryExpression $ Java.Identifier $ sanitizeJavaName otherInstanceName
            rt = nameToJavaReferenceType aliases False [] elName Nothing

        returnAllFieldsEqual = Java.BlockStatementStatement $ javaReturnStatement $ Just $ if L.null fields
            then javaBooleanExpression True
            else javaConditionalAndExpressionToJavaExpression $
              Java.ConditionalAndExpression (eqClause . fieldTypeName <$> fields)
          where
            eqClause (FieldName fname) = javaPostfixExpressionToJavaInclusiveOrExpression $
                javaMethodInvocationToJavaPostfixExpression $ Java.MethodInvocation header [arg]
              where
                arg = javaExpressionNameToJavaExpression $
                  fieldExpression (javaIdentifier tmpName) (javaIdentifier fname)
                header = Java.MethodInvocation_HeaderComplex $ Java.MethodInvocation_Complex var [] (Java.Identifier equalsMethodName)
                var = Java.MethodInvocation_VariantExpression $ Java.ExpressionName Nothing $ Java.Identifier $
                  sanitizeJavaName fname

    hashCodeMethod = methodDeclaration mods [] anns hashCodeMethodName [] result $ Just [returnSum]
      where
        anns = [overrideAnnotation]
        mods = [Java.MethodModifierPublic]
        result = javaTypeToJavaResult javaIntType

        returnSum = Java.BlockStatementStatement $ if L.null fields
          then returnZero
          else javaReturnStatement $ Just $
            javaAdditiveExpressionToJavaExpression $ addExpressions $
              L.zipWith multPair multipliers (fieldTypeName <$> fields)
          where
            returnZero = javaReturnStatement $ Just $ javaIntExpression 0

            multPair :: Int -> FieldName -> Java.MultiplicativeExpression
            multPair i (FieldName fname) = Java.MultiplicativeExpressionTimes $
                Java.MultiplicativeExpression_Binary lhs rhs
              where
                lhs = Java.MultiplicativeExpressionUnary $ javaPrimaryToJavaUnaryExpression $
                  javaLiteralToJavaPrimary $ javaInt i
                rhs = javaPostfixExpressionToJavaUnaryExpression $
                  javaMethodInvocationToJavaPostfixExpression $
                  methodInvocationStatic (javaIdentifier fname) (Java.Identifier hashCodeMethodName) []

            multipliers = L.cycle first20Primes
              where
                first20Primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

declarationForType :: Bool -> Aliases -> (Element, TypedTerm) -> Flow Graph Java.TypeDeclarationWithComments
declarationForType isSer aliases (el, TypedTerm _ term) = withTrace ("element " ++ unName (elementName el)) $ do
    t <- coreDecodeType term >>= adaptType javaLanguage
    cd <- toClassDecl False isSer aliases [] (elementName el) t
    comments <- commentsFromElement el
    return $ Java.TypeDeclarationWithComments (Java.TypeDeclarationClass cd) comments

declarationForUnionType :: Bool -> Aliases
  -> [Java.TypeParameter] -> Name -> [FieldType] -> Flow Graph Java.ClassDeclaration
declarationForUnionType isSer aliases tparams elName fields = do
    variantClasses <- CM.mapM (fmap augmentVariantClass . unionFieldClass) fields
    let variantDecls = Java.ClassBodyDeclarationClassMember . Java.ClassMemberDeclarationClass <$> variantClasses
    variantDecls' <- CM.zipWithM addComment variantDecls fields
    let otherDecls = noComment <$> [privateConstructor, toAcceptMethod True tparams, visitor, partialVisitor]
    tn <- typeNameDecl aliases elName
    let bodyDecls = [tn] ++ otherDecls ++ variantDecls'
    let mods = classModsPublic ++ [Java.ClassModifierAbstract]
    return $ javaClassDeclaration aliases tparams elName mods Nothing (interfaceTypes isSer) bodyDecls
  where
    privateConstructor = makeConstructor aliases elName True [] []
    unionFieldClass (FieldType fname ftype) = do
      let rtype = Types.record $ if isUnitType ftype then [] else [FieldType (FieldName valueFieldName) ftype]
      toClassDecl True isSer aliases [] (variantClassName False elName fname) rtype
    augmentVariantClass (Java.ClassDeclarationNormal cd) = Java.ClassDeclarationNormal $ cd {
        Java.normalClassDeclarationModifiers = [Java.ClassModifierPublic, Java.ClassModifierStatic, Java.ClassModifierFinal],
        Java.normalClassDeclarationExtends = Just $ nameToJavaClassType aliases True args elName Nothing,
        Java.normalClassDeclarationParameters = tparams,
        Java.normalClassDeclarationBody = newBody (Java.normalClassDeclarationBody cd)}
      where
        newBody (Java.ClassBody decls) = Java.ClassBody $ decls ++ [noComment $ toAcceptMethod False tparams]
        args = typeParameterToTypeArgument <$> tparams

    visitor = javaInterfaceDeclarationToJavaClassBodyDeclaration $
        Java.NormalInterfaceDeclaration mods ti vtparams extends body
      where
        mods = [Java.InterfaceModifierPublic]
        ti = Java.TypeIdentifier $ Java.Identifier visitorName
        vtparams = tparams ++ [javaTypeParameter visitorReturnParameter]
        extends = []
        body = Java.InterfaceBody (toVisitMethod . fieldTypeName <$> fields)
          where
            toVisitMethod fname = interfaceMethodDeclaration [] [] visitMethodName [variantInstanceParam fname] resultR Nothing

    partialVisitor = javaInterfaceDeclarationToJavaClassBodyDeclaration $
        Java.NormalInterfaceDeclaration {
            Java.normalInterfaceDeclarationModifiers = [Java.InterfaceModifierPublic],
            Java.normalInterfaceDeclarationIdentifier = Java.TypeIdentifier $ Java.Identifier partialVisitorName,
            Java.normalInterfaceDeclarationParameters = tparams ++ [javaTypeParameter visitorReturnParameter],
            Java.normalInterfaceDeclarationExtends =
              [Java.InterfaceType $ javaClassType ((typeParameterToReferenceType <$> tparams) ++ [visitorTypeVariable]) Nothing visitorName],
            Java.normalInterfaceDeclarationBody = Java.InterfaceBody $ otherwise:(toVisitMethod . fieldTypeName <$> fields)}
      where
        otherwise = interfaceMethodDeclaration defaultMod [] otherwiseMethodName [mainInstanceParam] resultR $ Just [throw]
          where
            typeArgs = typeParameterToTypeArgument <$> tparams
            throw = Java.BlockStatementStatement $ Java.StatementWithoutTrailing $
                Java.StatementWithoutTrailingSubstatementThrow $ Java.ThrowStatement $
                javaConstructorCall (javaConstructorName (Java.Identifier "IllegalStateException") Nothing) args Nothing
              where
                args = [javaAdditiveExpressionToJavaExpression $ addExpressions [
                  javaStringMultiplicativeExpression "Non-exhaustive patterns when matching: ",
                  Java.MultiplicativeExpressionUnary $ javaIdentifierToJavaUnaryExpression $ Java.Identifier "instance"]]

        toVisitMethod fname = interfaceMethodDeclaration defaultMod [] visitMethodName [variantInstanceParam fname] resultR $
            Just [returnOtherwise]
          where
            returnOtherwise = Java.BlockStatementStatement $ javaReturnStatement $ Just $
              javaPrimaryToJavaExpression $ Java.PrimaryNoNewArray $ Java.PrimaryNoNewArrayMethodInvocation $
              methodInvocation Nothing (Java.Identifier otherwiseMethodName) [javaIdentifierToJavaExpression $ Java.Identifier "instance"]

    defaultMod = [Java.InterfaceMethodModifierDefault]

    resultR = javaTypeToJavaResult $ Java.TypeReference visitorTypeVariable

    typeArgs = typeParameterToTypeArgument <$> tparams

    mainInstanceParam = javaTypeToJavaFormalParameter classRef $ FieldName instanceName
      where
        classRef = javaClassTypeToJavaType $
          nameToJavaClassType aliases False typeArgs elName Nothing

    variantInstanceParam fname = javaTypeToJavaFormalParameter classRef $ FieldName instanceName
      where
        classRef = javaClassTypeToJavaType $
          nameToJavaClassType aliases False typeArgs (variantClassName False elName fname) Nothing

elementJavaIdentifier :: Bool -> Bool -> Aliases -> Name -> Java.Identifier
elementJavaIdentifier isPrim isMethod aliases name = Java.Identifier $ if isPrim
    then (qualify $ capitalize local) ++ "." ++ applyMethodName
    else case ns of
      Nothing -> local
      Just n -> (qualify $ elementsClassName n) ++ sep ++ local
  where
    sep = if isMethod then "::" else "."
    qualify s = Java.unIdentifier $ nameToJavaName aliases $ unqualifyName $ QualifiedName ns s
    QualifiedName ns local = qualifyNameEager name

elementNameToFilePath :: Name -> FilePath
elementNameToFilePath name = nameToFilePath False (FileExtension "java") $ unqualifyName $ QualifiedName ns (sanitizeJavaName local)
  where
    QualifiedName ns local = qualifyNameEager name

elementsClassName :: Namespace -> String
elementsClassName (Namespace ns) = capitalize $ L.last $ LS.splitOn "/" ns

encodeApplication :: Aliases -> Application -> Flow Graph Java.Expression
encodeApplication aliases app@(Application lhs rhs) = case stripTerm fun of
    TermFunction f -> case f of
      FunctionPrimitive name -> functionCall aliases True name args
      _ -> fallback
    TermVariable name -> do
        firstCall <- functionCall aliases False name [L.head args]
        calls firstCall $ L.tail args
      where
        calls exp args = case args of
          [] -> pure exp
          (h:r) -> do
            jarg <- encodeTerm aliases h
            calls (apply exp jarg) r
    _ -> fallback
  where
    (fun, args) = uncurry [] lhs rhs
      where
       uncurry args lhs rhs = case stripTerm lhs of
         TermApplication (Application lhs' rhs') -> uncurry (rhs:args) lhs' rhs'
         _ -> (lhs, (rhs:args))

    fallback = do
        t <- requireTermType lhs
        (dom, cod) <- case stripTypeParameters $ stripType t of
            TypeFunction (FunctionType dom cod) -> pure (dom, cod)
            t' -> fail $ "expected a function type on function " ++ show lhs ++ ", but found " ++ show t'
        case stripTerm lhs of
          TermFunction f -> case f of
            FunctionElimination e -> do
                jarg <- encodeTerm aliases rhs
                encodeElimination aliases (Just jarg) dom cod e
            _ -> defaultExpression
          _ -> defaultExpression
      where
        defaultExpression = do
          -- Note: the domain type will not be used, so we just substitute the unit type
          jfun <- encodeTerm aliases lhs
          jarg <- encodeTerm aliases rhs
          let prim = javaExpressionToJavaPrimary jfun
          return $ apply jfun jarg
    apply exp jarg = javaMethodInvocationToJavaExpression $
      methodInvocation (Just $ Right $ javaExpressionToJavaPrimary exp) (Java.Identifier applyMethodName) [jarg]

encodeElimination :: Aliases -> Maybe Java.Expression -> Type -> Type -> Elimination -> Flow Graph Java.Expression
encodeElimination aliases marg dom cod elm = case elm of
  EliminationOptional (OptionalCases nothing just) -> do
    jnothing <- encodeTerm aliases nothing
    jjust <- encodeTerm aliases just
    let var = Name "m"

    let jobj = case marg of
                  Nothing -> Left $ javaIdentifierToJavaExpressionName $ variableToJavaIdentifier var
                  Just jarg -> Right $ javaExpressionToJavaPrimary jarg
    let jhead = javaMethodInvocationToJavaExpression $ methodInvocation
          (Just jobj)
          (Java.Identifier "map") [jjust]
    let jbody = javaMethodInvocationToJavaExpression $ methodInvocation
          (Just $ Right $ javaExpressionToJavaPrimary jhead)
          (Java.Identifier "orElse") [jnothing]
    castType <- adaptTypeToJavaAndEncode aliases (TypeFunction $ FunctionType dom cod) >>= javaTypeToJavaReferenceType
    return $ case marg of
      Nothing -> javaCastExpressionToJavaExpression $ javaCastExpression castType $
                       javaExpressionToJavaUnaryExpression $ javaLambda var jbody
      Just _ -> jbody
  EliminationRecord (Projection _ fname) -> do
    jdomr <- adaptTypeToJavaAndEncode aliases dom >>= javaTypeToJavaReferenceType
    jexp <- case marg of
      Nothing -> pure $ javaLambda var jbody
        where
          var = Name "r"
          jbody = javaExpressionNameToJavaExpression $
            fieldExpression (variableToJavaIdentifier var) (javaIdentifier $ unFieldName fname)
      Just jarg -> pure $ javaFieldAccessToJavaExpression $ Java.FieldAccess qual (javaIdentifier $ unFieldName fname)
        where
          qual = Java.FieldAccess_QualifierPrimary $ javaExpressionToJavaPrimary jarg
    return jexp
  EliminationProduct (TupleProjection arity idx) -> if arity > javaMaxTupleLength
      then fail $ "Tuple eliminations of arity greater than " ++ show javaMaxTupleLength ++ " are unsupported"
      else pure $ case marg of
        Nothing -> javaLambda var $ accessExpr $ javaIdentifierToJavaExpression $ variableToJavaIdentifier var
          where
            var = Name "w"
        Just jarg -> accessExpr jarg
    where
      accessExpr jarg = javaFieldAccessToJavaExpression $ Java.FieldAccess qual accessor
        where
          accessor = javaIdentifier $ "object" ++ show (idx + 1)
          qual = Java.FieldAccess_QualifierPrimary $ javaExpressionToJavaPrimary jarg
  EliminationUnion (CaseStatement tname def fields) -> do
     case marg of
      Nothing -> do
        let lhs = annotationClassSetTermType kvAnnotationClass (Just $ Types.function (TypeVariable tname) cod) $ Terms.elimination elm
        let var = "u"
        encodeTerm aliases $ Terms.lambda var $ Terms.apply lhs (Terms.var var)
        -- TODO: default value
      Just jarg -> applyElimination jarg
    where
      applyElimination jarg = do
          let prim = javaExpressionToJavaPrimary jarg
          let consId = innerClassRef aliases tname $ case def of
                Nothing -> visitorName
                Just _ -> partialVisitorName
          jcod <- adaptTypeToJavaAndEncode aliases cod
          rt <- javaTypeToJavaReferenceType jcod
          let targs = typeArgsOrDiamond $ javaTypeArgumentsForType dom ++ [Java.TypeArgumentReference rt]
          otherwiseBranches <- case def of
            Nothing -> pure []
            Just d -> do
              b <- otherwiseBranch jcod d
              return [b]
          visitBranches <- CM.mapM (visitBranch jcod) fields
          let body = Java.ClassBody $ otherwiseBranches ++ visitBranches
          let visitor = javaConstructorCall (javaConstructorName consId $ Just targs) [] (Just body)
          return $ javaMethodInvocationToJavaExpression $
            methodInvocation (Just $ Right prim) (Java.Identifier acceptMethodName) [visitor]
        where
          otherwiseBranch jcod d = do
            targs <- javaTypeArgumentsForNamedType tname
            let jdom = Java.TypeReference $ nameToJavaReferenceType aliases True targs tname Nothing
            let mods = [Java.MethodModifierPublic]
            let anns = [overrideAnnotation]
            let param = javaTypeToJavaFormalParameter jdom $ FieldName instanceName
            let result = Java.ResultType $ Java.UnannType jcod
            jret <- encodeTerm aliases d
            let returnStmt = Java.BlockStatementStatement $ javaReturnStatement $ Just jret
            return $ noComment $ methodDeclaration mods [] anns otherwiseMethodName [param] result (Just [returnStmt])

          visitBranch jcod field = do
            targs <- javaTypeArgumentsForNamedType tname
            let jdom = Java.TypeReference $ nameToJavaReferenceType aliases True targs tname (Just $ capitalize $ unFieldName $ fieldName field)
            let mods = [Java.MethodModifierPublic]
            let anns = [overrideAnnotation]
            let param = javaTypeToJavaFormalParameter jdom $ FieldName instanceName
            let result = Java.ResultType $ Java.UnannType jcod
            -- Note: the escaping is necessary because the instance.value field reference does not correspond to an actual Hydra projection term
            let value = Terms.var ("$" ++ instanceName ++ "." ++ valueFieldName)
            jret <- encodeTerm aliases $ contractTerm $ Terms.apply (fieldTerm field) value
            let returnStmt = Java.BlockStatementStatement $ javaReturnStatement $ Just jret
            return $ noComment $ methodDeclaration mods [] anns visitMethodName [param] result (Just [returnStmt])
  EliminationWrap name -> case marg of
    Nothing -> pure $ javaLambda var jbody
      where
        var = Name "w"
        arg = javaIdentifierToJavaExpression $ variableToJavaIdentifier var
        jbody = javaConstructorCall (javaConstructorName (nameToJavaName aliases name) Nothing) [arg] Nothing
    Just jarg -> pure $ javaFieldAccessToJavaExpression $ Java.FieldAccess qual (javaIdentifier valueFieldName)
      where
        qual = Java.FieldAccess_QualifierPrimary $ javaExpressionToJavaPrimary jarg
  _ -> pure $ encodeLiteral $ LiteralString $
    "Unimplemented elimination variant: " ++ show (eliminationVariant elm) -- TODO: temporary

encodeFunction :: Aliases -> Type -> Type -> Function -> Flow Graph Java.Expression
encodeFunction aliases dom cod fun = case fun of
  FunctionElimination elm -> do
    encodeElimination aliases Nothing dom cod elm
  FunctionLambda (Lambda var body) -> do
      lam <- toLambda var body
      if needsCast body
        then do
          jtype <- adaptTypeToJavaAndEncode aliases (TypeFunction $ FunctionType dom cod)
          rt <- javaTypeToJavaReferenceType jtype
          return $ javaCastExpressionToJavaExpression $
            javaCastExpression rt (javaExpressionToJavaUnaryExpression lam)
        else return lam
    where
      needsCast _  = True -- TODO: try to discriminate between lambdas which really need a cast, and those which do not
  _ -> pure $ encodeLiteral $ LiteralString $
    "Unimplemented function variant: " ++ show (functionVariant fun) -- TODO: temporary
  where
    toLambda var body = maybeLet aliases body cons
      where
        cons aliases' term stmts = if L.null stmts
          then do
            jbody <- encodeTerm aliases term
            return $ javaLambda var jbody
          else do
            jbody <- encodeTerm aliases term
            return $ javaLambdaFromBlock var $ Java.Block $ stmts
              ++ [Java.BlockStatementStatement $ javaReturnStatement $ Just jbody]

encodeLiteral :: Literal -> Java.Expression
encodeLiteral lit = javaLiteralToJavaExpression $ case lit of
  LiteralBoolean b -> javaBoolean b
  LiteralFloat f -> Java.LiteralFloatingPoint $ Java.FloatingPointLiteral $ case f of
    FloatValueFloat32 v -> realToFrac v
    FloatValueFloat64 v -> v
  LiteralInteger i -> case i of
      IntegerValueBigint v -> integer v -- BigInteger
      IntegerValueInt16 v -> integer $ fromIntegral v -- short
      IntegerValueInt32 v -> integer $ fromIntegral v -- int
      IntegerValueInt64 v -> integer $ fromIntegral v -- long
      IntegerValueUint8 v -> integer $ fromIntegral v -- byte
      IntegerValueUint16 v -> Java.LiteralCharacter $ fromIntegral v -- char
    where
      integer = Java.LiteralInteger . Java.IntegerLiteral
  LiteralString s -> javaString s

-- Note: we use Java object types everywhere, rather than primitive types, as the latter cannot be used
--       to build function types, parameterized types, etc.
encodeLiteralType :: LiteralType -> Flow Graph Java.Type
encodeLiteralType lt = case lt of
    LiteralTypeBoolean -> simple "Boolean"
    LiteralTypeFloat ft -> case ft of
      FloatTypeFloat32 -> simple "Float"
      FloatTypeFloat64 -> simple "Double"
      _ -> fail $ "unexpected float type: " ++ show ft
    LiteralTypeInteger it -> case it of
      IntegerTypeBigint -> pure $ javaRefType [] (Just $ javaPackageName ["java", "math"]) "BigInteger"
      IntegerTypeInt16 -> simple "Short"
      IntegerTypeInt32 -> simple "Integer"
      IntegerTypeInt64 -> simple "Long"
      IntegerTypeUint8 -> simple "Byte"
      IntegerTypeUint16 -> simple "Character"
      _ -> fail $ "unexpected integer type: " ++ show it
    LiteralTypeString -> simple "String"
    _ -> fail $ "unexpected literal type: " ++ show lt
  where
    simple n = pure $ javaRefType [] Nothing n

encodeNullaryConstant :: Aliases -> Type -> Function -> Flow Graph Java.Expression
encodeNullaryConstant aliases typ fun = case fun of
  FunctionPrimitive name -> functionCall aliases True name []
  _ -> unexpected "nullary function" $ show fun

encodeTerm :: Aliases -> Term -> Flow Graph Java.Expression
encodeTerm aliases term0 = encodeInternal [] term0
  where
    encode = encodeTerm aliases
    failAsLiteral msg = pure $ encodeLiteral $ LiteralString msg
    encodeInternal anns term = case term of
        TermAnnotated (Annotated term' ann) -> encodeInternal (ann:anns) term'

        TermApplication app -> encodeApplication aliases app

        TermFunction f -> withTrace "encode function" $ do
          t <- requireTermType term0
          case stripType t of
            TypeFunction (FunctionType dom cod) -> do
              encodeFunction aliases dom cod f
            _ -> encodeNullaryConstant aliases t f

        TermLet _ -> fail "nested let is unsupported for Java"

        TermList els -> do
          jels <- CM.mapM encode els
          return $ javaMethodInvocationToJavaExpression $
            methodInvocationStatic (Java.Identifier "java.util.Arrays") (Java.Identifier "asList") jels

        TermLiteral l -> pure $ encodeLiteral l

        TermOptional mt -> case mt of
          Nothing -> pure $ javaMethodInvocationToJavaExpression $
            methodInvocationStatic (Java.Identifier "java.util.Optional") (Java.Identifier "empty") []
          Just term1 -> do
            expr <- encode term1
            return $ javaMethodInvocationToJavaExpression $
              methodInvocationStatic (Java.Identifier "java.util.Optional") (Java.Identifier "of") [expr]

        TermProduct terms -> do
          jterms <- CM.mapM encode terms
          let tupleTypeName = "hydra.core.Tuple.Tuple" ++ show (length terms)
          return $ javaConstructorCall (javaConstructorName (Java.Identifier tupleTypeName) Nothing) jterms Nothing

        TermRecord (Record name fields) -> do
          fieldExprs <- CM.mapM encode (fieldTerm <$> fields)
          let consId = nameToJavaName aliases name
          return $ javaConstructorCall (javaConstructorName consId Nothing) fieldExprs Nothing

        TermSet s -> do
          jels <- CM.mapM encode $ S.toList s
          let prim = javaMethodInvocationToJavaPrimary $
                     methodInvocationStatic (Java.Identifier "java.util.Stream") (Java.Identifier "of") jels
          let coll = javaMethodInvocationToJavaExpression $
                     methodInvocationStatic (Java.Identifier "java.util.stream.Collectors") (Java.Identifier "toSet") []
          return $ javaMethodInvocationToJavaExpression $
            methodInvocation (Just $ Right prim) (Java.Identifier "collect") [coll]

        TermUnion (Injection name (Field (FieldName fname) v)) -> do
          let (Java.Identifier typeId) = nameToJavaName aliases name
          let consId = Java.Identifier $ typeId ++ "." ++ sanitizeJavaName (capitalize fname)
          args <- if isUnitTerm v
            then return []
            else do
              ex <- encode v
              return [ex]
          return $ javaConstructorCall (javaConstructorName consId Nothing) args Nothing

        TermVariable name -> encodeVariable aliases name

        TermWrap (Nominal tname arg) -> do
          jarg <- encode arg
          return $ javaConstructorCall (javaConstructorName (nameToJavaName aliases tname) Nothing) [jarg] Nothing

        _ -> failAsLiteral $ "Unimplemented term variant: " ++ show (termVariant term)

encodeType :: Aliases -> Type -> Flow Graph Java.Type
encodeType aliases t = case stripType t of
    TypeApplication (ApplicationType lhs rhs) -> do
      jlhs <- encode lhs
      jrhs <- encode rhs >>= javaTypeToJavaReferenceType
      addJavaTypeParameter jrhs jlhs
    TypeFunction (FunctionType dom cod) -> do
      jdom <- encode dom >>= javaTypeToJavaReferenceType
      jcod <- encode cod >>= javaTypeToJavaReferenceType
      return $ javaRefType [jdom, jcod] javaUtilFunctionPackageName "Function"
    TypeLambda (LambdaType (Name v) body) -> do
      jbody <- encode body
      addJavaTypeParameter (javaTypeVariable v) jbody
    TypeList et -> do
      jet <- encode et
      if listsAsArrays
        then toJavaArrayType jet
        else do
          rt <- javaTypeToJavaReferenceType jet
          return $ javaRefType [rt] javaUtilPackageName "List"
    TypeLiteral lt -> encodeLiteralType lt
    TypeMap (MapType kt vt) -> do
      jkt <- encode kt >>= javaTypeToJavaReferenceType
      jvt <- encode vt >>= javaTypeToJavaReferenceType
      return $ javaRefType [jkt, jvt] javaUtilPackageName "Map"
    TypeProduct types ->
      case types of
        [] -> unit
        _ -> do
          jtypes <- CM.mapM encode types >>= mapM javaTypeToJavaReferenceType
          return $ javaRefType jtypes hydraCorePackageName $ "Tuple.Tuple" ++ (show $ length types)
    TypeRecord (RowType _UnitType _ []) -> unit
    TypeRecord (RowType name _ _) -> pure $
      Java.TypeReference $ nameToJavaReferenceType aliases True (javaTypeArgumentsForType t) name Nothing
    TypeOptional ot -> do
      jot <- encode ot >>= javaTypeToJavaReferenceType
      return $ javaRefType [jot] javaUtilPackageName "Optional"
    TypeSet st -> do
      jst <- encode st >>= javaTypeToJavaReferenceType
      return $ javaRefType [jst] javaUtilPackageName "Set"
    TypeUnion (RowType name _ _) -> pure $
      Java.TypeReference $ nameToJavaReferenceType aliases True (javaTypeArgumentsForType t) name Nothing
    TypeVariable name -> forReference name
    TypeWrap (Nominal name _) -> forReference name
    _ -> fail $ "can't encode unsupported type in Java: " ++ show t
  where
    forReference name = pure $ if isLambdaBoundVariable name
        then variableReference name
        else nameReference name
    nameReference name = Java.TypeReference $ nameToJavaReferenceType aliases True [] name Nothing
    variableReference name = Java.TypeReference $ javaTypeVariable $ unName name
    encode = encodeType aliases
    unit = return $ javaRefType [] javaLangPackageName "Void"

encodeVariable :: Aliases -> Name -> Flow Graph Java.Expression
encodeVariable aliases name = if isRecursiveVariable aliases name
    then return $ javaMethodInvocationToJavaExpression $
      methodInvocation (Just $ Left $ Java.ExpressionName Nothing jid) (Java.Identifier getMethodName) []
    else do
      cls <- classifyDataReference name
      return $ case cls of
        JavaSymbolLocalVariable -> javaIdentifierToJavaExpression $ elementJavaIdentifier False False aliases name
        JavaSymbolClassConstant -> javaIdentifierToJavaExpression $ elementJavaIdentifier False False aliases name
        JavaSymbolClassNullaryFunction -> javaIdentifierToJavaExpression $ elementJavaIdentifier False True aliases name -- TODO
        JavaSymbolClassUnaryFunction -> javaIdentifierToJavaExpression $ elementJavaIdentifier False True aliases name
  where
    jid = javaIdentifier $ unName name

fieldTypeToFormalParam aliases (FieldType fname ft) = do
  jt <- adaptTypeToJavaAndEncode aliases ft
  return $ javaTypeToJavaFormalParameter jt fname

functionCall :: Aliases -> Bool -> Name -> [Term] -> Flow Graph Java.Expression
functionCall aliases isPrim name args = do
    jargs <- CM.mapM (encodeTerm aliases) args
    if isLocalVariable name
      then do
        prim <- javaExpressionToJavaPrimary <$> encodeVariable aliases name
        return $ javaMethodInvocationToJavaExpression $
          methodInvocation (Just $ Right prim) (Java.Identifier applyMethodName) jargs
      else do
        let header = Java.MethodInvocation_HeaderSimple $ Java.MethodName $ elementJavaIdentifier isPrim False aliases name
        return $ javaMethodInvocationToJavaExpression $ Java.MethodInvocation header jargs

getCodomain :: Kv -> Flow Graph Type
getCodomain ann = functionTypeCodomain <$> getFunctionType ann

getFunctionType :: Kv -> Flow Graph (FunctionType)
getFunctionType ann = do
  mt <- annotationClassTypeOf kvAnnotationClass ann
  case mt of
    Nothing -> fail "type annotation is required for function and elimination terms in Java"
    Just t -> case t of
      TypeFunction ft -> return ft
      _ -> unexpected "function type (3)" $ show t

innerClassRef :: Aliases -> Name -> String -> Java.Identifier
innerClassRef aliases name local = Java.Identifier $ id ++ "." ++ local
  where
    Java.Identifier id = nameToJavaName aliases name

interfaceTypes :: Bool -> [Java.InterfaceType]
interfaceTypes isSer = if isSer then [javaSerializableType] else []
  where
    javaSerializableType = Java.InterfaceType $
      Java.ClassType [] Java.ClassTypeQualifierNone (javaTypeIdentifier "Serializable") []

isLambdaBoundVariable :: Name -> Bool
isLambdaBoundVariable (Name v) = L.length v <= 4

isLocalVariable :: Name -> Bool
isLocalVariable name = Y.isNothing $ qualifiedNameNamespace $ qualifyNameEager name

isRecursiveVariable :: Aliases -> Name -> Bool
isRecursiveVariable aliases name = S.member name (aliasesRecursiveVars aliases)

javaTypeArgumentsForNamedType :: Name -> Flow Graph [Java.TypeArgument]
javaTypeArgumentsForNamedType tname = do
    params <- javaTypeParametersForType <$> requireType tname
    return $ typeParameterToTypeArgument <$> params

javaTypeArgumentsForType :: Type -> [Java.TypeArgument]
javaTypeArgumentsForType typ = L.reverse (typeParameterToTypeArgument <$> javaTypeParametersForType typ)

-- Note: this is somewhat of a hack; it compensates for the irregular way in which type parameters are currently used.
--       When this irregularity is resolved, a better approach will be to simply pick up type parameters from type applications.
javaTypeParametersForType :: Type -> [Java.TypeParameter]
javaTypeParametersForType typ = toParam <$> vars
  where
    toParam (Name v) = Java.TypeParameter [] (javaTypeIdentifier $ capitalize v) Nothing
    vars = L.nub $ boundVars typ ++ freeVars
    boundVars t = case stripType t of
      TypeLambda (LambdaType v body) -> v:(boundVars body)
      _ -> []
    freeVars = L.filter isLambdaBoundVariable $ S.toList $ freeVariablesInType typ

maybeLet :: Aliases -> Term -> (Aliases -> Term -> [Java.BlockStatement] -> Flow Graph x) -> Flow Graph x
maybeLet aliases term cons = helper [] term
  where
    helper anns term = case term of
      TermAnnotated (Annotated term' ann) -> helper (ann:anns) term'
      TermLet (Let bindings env) -> do
          stmts <- L.concat <$> CM.mapM toDeclStatements sorted
          maybeLet aliasesWithRecursive env $ \aliases' tm stmts' -> cons aliases' (reannotate anns tm) (stmts ++ stmts')
        where
          aliasesWithRecursive = aliases { aliasesRecursiveVars = recursiveVars }
          toDeclStatements names = do
            inits <- Y.catMaybes <$> CM.mapM toDeclInit names
            impls <- CM.mapM toDeclStatement names
            return $ inits ++ impls

          toDeclInit name = if S.member name recursiveVars
            then do
              -- TODO: repeated
              let value = Y.fromJust $ M.lookup name bindings
              typ <- requireAnnotatedType value
              jtype <- adaptTypeToJavaAndEncode aliasesWithRecursive typ
              let id = variableToJavaIdentifier name

              let pkg = javaPackageName ["java", "util", "concurrent", "atomic"]
              let arid = Java.Identifier "java.util.concurrent.atomic.AtomicReference" -- TODO
              let aid = Java.AnnotatedIdentifier [] arid
              rt <- javaTypeToJavaReferenceType jtype
              let targs = typeArgsOrDiamond [Java.TypeArgumentReference rt]
              let ci = Java.ClassOrInterfaceTypeToInstantiate [aid] (Just targs)
              let body = javaConstructorCall ci [] Nothing
              let artype = javaRefType [rt] (Just pkg) "AtomicReference"
              return $ Just $ variableDeclarationStatement aliasesWithRecursive artype id body
            else pure Nothing

          toDeclStatement name = do
            -- TODO: repeated
            let value = Y.fromJust $ M.lookup name bindings
            typ <- requireAnnotatedType value
            jtype <- adaptTypeToJavaAndEncode aliasesWithRecursive typ
            let id = variableToJavaIdentifier name
            rhs <- encodeTerm aliasesWithRecursive value
            return $ if S.member name recursiveVars
              then Java.BlockStatementStatement $ javaMethodInvocationToJavaStatement $
                methodInvocation (Just $ Left $ Java.ExpressionName Nothing id) (Java.Identifier setMethodName) [rhs]
              else variableDeclarationStatement aliasesWithRecursive jtype id rhs
          bindingVars = S.fromList $ M.keys bindings
          recursiveVars = S.fromList $ L.concat (ifRec <$> sorted)
            where
              ifRec names = case names of
                [name] -> case M.lookup name allDeps of
                  Nothing -> []
                  Just deps -> if S.member name deps
                    then [name]
                    else []
                _ -> names
          allDeps = M.fromList (toDeps <$> M.toList bindings)
            where
              toDeps (key, value) = (key, S.filter (\n -> S.member n bindingVars) $ freeVariablesInTerm value)
          sorted = topologicalSortComponents (toDeps <$> M.toList allDeps)
            where
              toDeps (key, deps) = (key, S.toList deps)
      _ -> cons aliases (reannotate anns term) []

moduleToJavaCompilationUnit :: Module -> Flow Graph (M.Map Name Java.CompilationUnit)
moduleToJavaCompilationUnit mod = transformModule javaLanguage encode constructModule mod
  where
    aliases = importAliasesForModule mod
    encode = encodeTerm aliases . contractTerm

noComment :: Java.ClassBodyDeclaration -> Java.ClassBodyDeclarationWithComments
noComment decl = Java.ClassBodyDeclarationWithComments decl Nothing

reannotate anns term = case anns of
  [] -> term
  (h:r) -> reannotate r $ TermAnnotated (Annotated term h)

requireAnnotatedType :: Term -> Flow Graph Type
requireAnnotatedType term = case term of
  TermAnnotated (Annotated _ ann) -> do
    mt <- annotationClassTypeOf kvAnnotationClass ann
    case mt of
      Nothing -> fail $ "expected a type annotation for term: " ++ show term
      Just t -> pure t

toClassDecl :: Bool -> Bool -> Aliases -> [Java.TypeParameter]
  -> Name -> Type -> Flow Graph Java.ClassDeclaration
toClassDecl isInner isSer aliases tparams elName t = case stripType t of
    TypeRecord rt -> declarationForRecordType isInner isSer aliases tparams elName $ rowTypeFields rt
    TypeUnion rt -> declarationForUnionType isSer aliases tparams elName $ rowTypeFields rt
    TypeLambda ut -> declarationForLambdaType isSer aliases tparams elName ut
    TypeWrap (Nominal tname wt) -> declarationForRecordType isInner isSer aliases tparams elName
      [FieldType (FieldName "value") wt]
    -- Other types are not supported as class declarations, so we wrap them as record types.
    _ -> wrap t -- TODO: wrap and unwrap the corresponding terms as record terms.
  where
    wrap t' = declarationForRecordType isInner isSer aliases tparams elName [Types.field valueFieldName t']

toDataDeclaration :: Aliases -> (a, TypedTerm) -> Flow Graph a
toDataDeclaration aliases (el, TypedTerm typ term) = do
  fail "not implemented" -- TODO

typeArgsOrDiamond :: [Java.TypeArgument] -> Java.TypeArgumentsOrDiamond
typeArgsOrDiamond args = if supportsDiamondOperator javaFeatures
  then Java.TypeArgumentsOrDiamondDiamond
  else Java.TypeArgumentsOrDiamondArguments args

typeNameDecl :: Aliases -> Name -> Flow Graph Java.ClassBodyDeclarationWithComments
typeNameDecl aliases name = do
  jt <- adaptTypeToJavaAndEncode aliases $ TypeVariable _Name
  arg <- encodeTerm aliases $ Terms.string $ unName name
  let init = Java.VariableInitializerExpression $ javaConstructorCall (javaConstructorName nameName Nothing) [arg] Nothing
  let var = javaVariableDeclarator (Java.Identifier "NAME") (Just init)
  return $ noComment $ javaMemberField mods jt var
  where
    mods = [Java.FieldModifierPublic, Java.FieldModifierStatic, Java.FieldModifierFinal]
    nameName = nameToJavaName aliases _Name
