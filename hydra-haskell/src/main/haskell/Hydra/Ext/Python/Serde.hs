module Hydra.Ext.Python.Serde where

import qualified Hydra.Ext.Python.Syntax as Py
import Hydra.Tools.Serialization
import qualified Hydra.Ast as A

import qualified Data.List as L
import qualified Data.Maybe as Y


encodeAnnotatedRhs :: Py.AnnotatedRhs -> A.Expr
encodeAnnotatedRhs a = spaceSep [cst "=", case a of
  Py.AnnotatedRhsStar s -> commaSep inlineStyle (encodeStarExpression <$> s)
  _ -> unsupportedVariant "annotated rhs" a]

encodeAnnotatedStatement :: Py.AnnotatedStatement -> A.Expr
encodeAnnotatedStatement (Py.AnnotatedStatement doc stmt) = newlineSep [cst $ toPythonComments doc, encodeStatement stmt]

encodeArgs :: Py.Args -> A.Expr
encodeArgs (Py.Args positional kwargStarred kwargDoubleStarred) = commaSep inlineStyle $ ps ++ ks ++ kss
  where
    ps = encodePosArg <$> positional
    ks = encodeKwargOrStarred <$> kwargStarred
    kss = encodeKwargOrDoubleStarred <$> kwargDoubleStarred

encodeAssignment :: Py.Assignment -> A.Expr
encodeAssignment a = case a of
  Py.AssignmentTyped t -> encodeTypedAssignment t
  Py.AssignmentUntyped u -> encodeUntypedAssignment u
  _ -> unsupportedVariant "assignment" a

encodeAssignmentExpression :: Py.AssignmentExpression -> A.Expr
encodeAssignmentExpression (Py.AssignmentExpression name expr)
  = spaceSep [encodeName name, cst ":=", encodeExpression expr]

encodeAtom :: Py.Atom -> A.Expr
encodeAtom a = case a of
  Py.AtomDict d -> encodeDict d
  Py.AtomList l -> encodeList l
  Py.AtomName n -> encodeName n
  Py.AtomString s -> cst $ escapePythonString True s
  _ -> unsupportedVariant "atom" a

encodeAwaitPrimary :: Py.AwaitPrimary -> A.Expr
encodeAwaitPrimary (Py.AwaitPrimary await primary) = if await
  then spaceSep [cst "await", encodePrimary primary]
  else encodePrimary primary

encodeBitwiseAnd :: Py.BitwiseAnd -> A.Expr
encodeBitwiseAnd (Py.BitwiseAnd lhs rhs) = spaceSep $ Y.catMaybes [encodeLhs <$> lhs, Just $ encodeShiftExpression rhs]
  where
    encodeLhs l = spaceSep [encodeBitwiseAnd l, cst "&"]

encodeBitwiseOr :: Py.BitwiseOr -> A.Expr
encodeBitwiseOr (Py.BitwiseOr lhs rhs) = spaceSep $ Y.catMaybes [encodeLhs <$> lhs, Just $ encodeBitwiseXor rhs]
  where
    encodeLhs l = spaceSep [encodeBitwiseOr l, cst "|"]

encodeBitwiseXor :: Py.BitwiseXor -> A.Expr
encodeBitwiseXor (Py.BitwiseXor lhs rhs) = spaceSep $ Y.catMaybes [encodeLhs <$> lhs, Just $ encodeBitwiseAnd rhs]
  where
    encodeLhs l = spaceSep [encodeBitwiseXor l, cst "^"]

encodeBlock :: Bool -> Py.Block -> A.Expr
encodeBlock doubleSpace b = case b of
  Py.BlockIndented sc -> (if doubleSpace then tabIndentDoubleSpace else tabIndentSingleSpace) (encodeStatement <$> sc)
  Py.BlockSimple ss -> (if doubleSpace then doubleNewlineSep else newlineSep) (encodeSimpleStatement <$> ss)

encodeClassDefinition :: Py.ClassDefinition -> A.Expr
encodeClassDefinition (Py.ClassDefinition mdecs name tparams args comment body) = newlineSep $
  Y.catMaybes [encodeDecorators <$> mdecs, Just classExpr]
  where
    classExpr = newlineSep [
        noSep [spaceSep $ Y.catMaybes [Just $ cst "class", Just $ encodeName name, (argExp <$> args)], cst ":"],
        doubleNewlineSep $ Y.catMaybes [
          (\c -> tabIndent (tripleQuotedString c)) <$> comment,
          Just $ encodeBlock False body]] -- TODO: tparams
      where
        argExp a = noSep [cst "(", encodeArgs a, cst ")"]

encodeCompareOpBitwiseOrPair :: Py.CompareOpBitwiseOrPair -> A.Expr
encodeCompareOpBitwiseOrPair p = unsupportedType "compare op bitwise or pair"

encodeComparison :: Py.Comparison -> A.Expr
encodeComparison (Py.Comparison lhs rhs) = spaceSep $ [encodeBitwiseOr lhs] ++ (encodeCompareOpBitwiseOrPair <$> rhs)

encodeCompoundStatement :: Py.CompoundStatement -> A.Expr
encodeCompoundStatement c = case c of
  Py.CompoundStatementClassDef d -> encodeClassDefinition d
  _ -> unsupportedVariant "compound statement" c

encodeConjunction :: Py.Conjunction -> A.Expr
encodeConjunction (Py.Conjunction is) = symbolSep "and" inlineStyle (encodeInversion <$> is)

encodeDecorators :: Py.Decorators -> A.Expr
encodeDecorators (Py.Decorators exprs) = newlineSep (encodeDec <$> exprs)
  where
    encodeDec ne = noSep [cst "@", encodeNamedExpression ne]

encodeDict :: Py.Dict -> A.Expr
encodeDict (Py.Dict items) = noSep [cst "{", commaSep inlineStyle (encodeDoubleStarredKvpair <$> items), cst "}"]

encodeDisjunction :: Py.Disjunction -> A.Expr
encodeDisjunction (Py.Disjunction cs) = symbolSep "or" inlineStyle (encodeConjunction <$> cs)

encodeDottedAsName :: Py.DottedAsName -> A.Expr
encodeDottedAsName (Py.DottedAsName name mas) = spaceSep $ Y.catMaybes [Just $ encodeDottedName name, encodeName <$> mas]
  where
    encodeAs a = spaceSep [cst "as", encodeName a]

encodeDottedName :: Py.DottedName -> A.Expr
encodeDottedName (Py.DottedName names) = cst $ L.intercalate "." (Py.unName <$> names)

encodeDoubleStarredKvpair :: Py.DoubleStarredKvpair -> A.Expr
encodeDoubleStarredKvpair d = case d of
  Py.DoubleStarredKvpairPair p -> encodeKvpair p
  _ -> unsupportedVariant "double starred kv pair" d

encodeExpression :: Py.Expression -> A.Expr
encodeExpression e = case e of
  Py.ExpressionSimple d -> encodeDisjunction d
  _ -> unsupportedVariant "expression" e

encodeFactor :: Py.Factor -> A.Expr
encodeFactor f = case f of
  Py.FactorPositive f -> noSep [cst "+", encodeFactor f]
  Py.FactorNegative f -> noSep [cst "-", encodeFactor f]
  Py.FactorComplement f -> noSep [cst "~", encodeFactor f]
  Py.FactorSimple p -> encodePower p

encodeImportFrom :: Py.ImportFrom -> A.Expr
encodeImportFrom (Py.ImportFrom prefixes name targets) = spaceSep [cst "from", lhs, cst "import", rhs]
  where
    lhs = noSep $ Y.catMaybes $ (Just . encodeRelativeImportPrefix <$> prefixes) ++ [encodeDottedName <$> name]
    rhs = encodeImportFromTargets targets

encodeImportFromAsName :: Py.ImportFromAsName -> A.Expr
encodeImportFromAsName (Py.ImportFromAsName name malias) = case malias of
  Nothing -> encodeName name
  Just a -> spaceSep [encodeName name, cst "as", encodeName a]

encodeImportFromTargets :: Py.ImportFromTargets -> A.Expr
encodeImportFromTargets i = case i of
    Py.ImportFromTargetsSimple t -> names t
    Py.ImportFromTargetsParens t -> noSep [cst "(", names t, cst ")"]
    Py.ImportFromTargetsStar -> cst "*"
  where
    names :: [Py.ImportFromAsName] -> A.Expr
    names t = commaSep inlineStyle (encodeImportFromAsName <$> t)

encodeImportName :: Py.ImportName -> A.Expr
encodeImportName (Py.ImportName dans) = spaceSep [cst "import", commaSep inlineStyle (encodeDottedAsName <$> dans)]

encodeImportStatement :: Py.ImportStatement -> A.Expr
encodeImportStatement s = case s of
  Py.ImportStatementName n -> encodeImportName n
  Py.ImportStatementFrom i -> encodeImportFrom i

encodeInversion :: Py.Inversion -> A.Expr
encodeInversion i = case i of
  Py.InversionNot other -> spaceSep [cst "not", encodeInversion other]
  Py.InversionSimple c -> encodeComparison c

encodeKvpair :: Py.Kvpair -> A.Expr
encodeKvpair (Py.Kvpair k v) = spaceSep [noSep [encodeExpression k, cst ":"], encodeExpression v]

encodeKwarg :: Py.Kwarg -> A.Expr
encodeKwarg (Py.Kwarg name expr) = noSep [encodeName name, cst "=", encodeExpression expr]

encodeKwargOrDoubleStarred :: Py.KwargOrDoubleStarred -> A.Expr
encodeKwargOrDoubleStarred k = case k of
  Py.KwargOrDoubleStarredKwarg kw -> encodeKwarg kw
  Py.KwargOrDoubleStarredDoubleStarred e -> noSep [cst "**", encodeExpression e]

encodeKwargOrStarred :: Py.KwargOrStarred -> A.Expr
encodeKwargOrStarred k = case k of
  Py.KwargOrStarredKwarg kw -> encodeKwarg kw
  Py.KwargOrStarredStarred se -> encodeStarredExpression se

encodeList :: Py.List -> A.Expr
encodeList (Py.List es) = noSep [cst "[", commaSep inlineStyle (encodeStarNamedExpression <$> es), cst "]"]

encodeModule :: Py.Module -> A.Expr
encodeModule (Py.Module imports mdoc body) = doubleNewlineSep $ Y.catMaybes $
   [tripleQuotedString <$> mdoc, importsSec] ++ bodyExprs
  where
    bodyExprs = Just . encodeStatement <$> body
    importsSec = if L.null exprs then Nothing else Just $ newlineSep exprs
      where
        exprs = encodeImportStatement <$> imports

encodeName :: Py.Name -> A.Expr
encodeName (Py.Name n) = cst n

encodeNamedExpression :: Py.NamedExpression -> A.Expr
encodeNamedExpression ne = case ne of
  Py.NamedExpressionSimple e -> encodeExpression e
  _ -> unsupportedVariant "named expression" ne

encodePosArg :: Py.PosArg -> A.Expr
encodePosArg a = case a of
  Py.PosArgStarred se -> encodeStarredExpression se
  Py.PosArgAssignment ae -> encodeAssignmentExpression ae
  Py.PosArgExpression e -> encodeExpression e

encodePower :: Py.Power -> A.Expr
encodePower (Py.Power lhs rhs) = spaceSep $ Y.catMaybes [Just $ encodeAwaitPrimary lhs, encodeRhs <$> rhs]
  where
    encodeRhs r = spaceSep [cst "**", encodeFactor r]

encodePrimary :: Py.Primary -> A.Expr
encodePrimary p = case p of
  Py.PrimarySimple a -> encodeAtom a
  Py.PrimaryCompound p -> encodePrimaryWithRhs p

encodePrimaryRhs :: Py.PrimaryRhs -> A.Expr
encodePrimaryRhs p = case p of
  Py.PrimaryRhsCall args -> noSep [cst "(", encodeArgs args, cst ")"]
  Py.PrimaryRhsSlices slices -> noSep [cst "[", encodeSlices slices, cst "]"]
  _ -> unsupportedVariant "primary rhs" p

encodePrimaryWithRhs :: Py.PrimaryWithRhs -> A.Expr
encodePrimaryWithRhs (Py.PrimaryWithRhs primary rhs) = noSep [encodePrimary primary, encodePrimaryRhs rhs]

encodeRelativeImportPrefix :: Py.RelativeImportPrefix -> A.Expr
encodeRelativeImportPrefix p = cst $ case p of
  Py.RelativeImportPrefixDot -> "."
  Py.RelativeImportPrefixEllipsis -> "..."

encodeShiftExpression :: Py.ShiftExpression -> A.Expr
encodeShiftExpression (Py.ShiftExpression lhs rhs) = spaceSep $ Y.catMaybes [encodeShiftLhs <$> lhs, Just $ encodeSum rhs]

encodeShiftLhs :: Py.ShiftLhs -> A.Expr
encodeShiftLhs l = unsupportedType "shift lhs"

encodeSimpleStatement :: Py.SimpleStatement -> A.Expr
encodeSimpleStatement s = case s of
  Py.SimpleStatementAssignment a -> encodeAssignment a
  Py.SimpleStatementImport i -> encodeImportStatement i
  Py.SimpleStatementTypeAlias t -> encodeTypeAlias t
  _ -> unsupportedVariant "simple statement" s

encodeSingleTarget :: Py.SingleTarget -> A.Expr
encodeSingleTarget s = case s of
  Py.SingleTargetName n -> encodeName n
  _ -> unsupportedVariant "single target" s

encodeSlice :: Py.Slice -> A.Expr
encodeSlice s = case s of
  Py.SliceNamed n -> encodeNamedExpression n
  _ -> unsupportedVariant "slice" s

encodeSliceOrStarredExpression :: Py.SliceOrStarredExpression -> A.Expr
encodeSliceOrStarredExpression s = case s of
  Py.SliceOrStarredExpressionSlice s -> encodeSlice s
  Py.SliceOrStarredExpressionStarred e -> encodeStarredExpression e

encodeSlices :: Py.Slices -> A.Expr
encodeSlices (Py.Slices head tail) = commaSep inlineStyle (ehead:etail)
  where
    ehead = encodeSlice head
    etail = encodeSliceOrStarredExpression <$> tail

encodeStarAtom :: Py.StarAtom -> A.Expr
encodeStarAtom a = case a of
  Py.StarAtomName n -> encodeName n
  _ -> unsupportedVariant "star atom" a

encodeStarExpression :: Py.StarExpression -> A.Expr
encodeStarExpression s = case s of
  Py.StarExpressionSimple e -> encodeExpression e
  _ -> unsupportedVariant "star expression" s

encodeStarNamedExpression :: Py.StarNamedExpression -> A.Expr
encodeStarNamedExpression s = case s of
  Py.StarNamedExpressionStar bor -> noSep [cst "*", encodeBitwiseOr bor]
  Py.StarNamedExpressionSimple ne -> encodeNamedExpression ne

encodeStarTarget :: Py.StarTarget -> A.Expr
encodeStarTarget s = case s of
  Py.StarTargetUnstarred t -> encodeTargetWithStarAtom t
  _ -> unsupportedVariant "star target" s

encodeStarredExpression :: Py.StarredExpression -> A.Expr
encodeStarredExpression (Py.StarredExpression expr) = noSep [cst "*", encodeExpression expr]

encodeStatement :: Py.Statement -> A.Expr
encodeStatement s = case s of
  Py.StatementAnnotated a -> encodeAnnotatedStatement a
  Py.StatementCompound c -> encodeCompoundStatement c
  Py.StatementSimple stmts -> newlineSep (encodeSimpleStatement <$> stmts)

encodeSum :: Py.Sum -> A.Expr
encodeSum (Py.Sum lhs rhs) = spaceSep $ Y.catMaybes [encodeSumLhs <$> lhs, Just $ encodeTerm rhs]

encodeSumLhs :: Py.SumLhs -> A.Expr
encodeSumLhs l = unsupportedType "sum lhs"

encodeTerm :: Py.Term -> A.Expr
encodeTerm (Py.Term lhs rhs) = spaceSep $ Y.catMaybes [encodeTermLhs <$> lhs, Just $ encodeFactor rhs]

encodeTermLhs :: Py.TermLhs -> A.Expr
encodeTermLhs l = unsupportedType "term lhs"

encodeTargetWithStarAtom :: Py.TargetWithStarAtom -> A.Expr
encodeTargetWithStarAtom t = case t of
  Py.TargetWithStarAtomAtom a -> encodeStarAtom a
  _ -> unsupportedVariant "target with star atom" t

encodeTypeAlias :: Py.TypeAlias -> A.Expr
encodeTypeAlias (Py.TypeAlias name tparams body) = spaceSep [cst "type", encodeName name, cst "=", encodeExpression body]

encodeTypedAssignment :: Py.TypedAssignment -> A.Expr
encodeTypedAssignment (Py.TypedAssignment lhs typ rhs) = spaceSep $ Y.catMaybes [
    Just head, Just $ encodeExpression typ, encodeAnnotatedRhs <$> rhs]
  where
    head = noSep [encodeSingleTarget lhs, cst ":"]

encodeUntypedAssignment :: Py.UntypedAssignment -> A.Expr
encodeUntypedAssignment (Py.UntypedAssignment targets rhs _) = spaceSep $ lefts ++ [right]
  where
    lefts = encodeStarTarget <$> targets
    right = encodeAnnotatedRhs rhs

-- TODO: this is a partially ChatGPT-generated function which has not been thoroughly tested.
escapePythonString :: Bool -> String -> String
escapePythonString doubleQuoted str = encChar : L.concatMap escapeChar str ++ [encChar]
  where
    encChar = if doubleQuoted then '"' else '\''
    escapeChar '\'' = if doubleQuoted then  "'" else "\\'"  -- Escape single quote
    escapeChar '"'  = if doubleQuoted then "\\\"" else "\""  -- Escape double quote
    escapeChar '\\' = "\\\\" -- Escape backslash
    escapeChar '\n' = "\\n"  -- Escape newline
    escapeChar '\t' = "\\t"  -- Escape tab
    escapeChar '\r' = "\\r"  -- Escape carriage return
    escapeChar c
      | c < ' '   = "\\x" ++ toHex (fromEnum c) -- Escape other control chars as hex
      | otherwise = [c]  -- Leave normal characters as is

    toHex :: Int -> String
    toHex n = let hex = "0123456789abcdef"
              in [hex !! (n `div` 16), hex !! (n `mod` 16)]

toPythonComments :: String -> String
toPythonComments c = L.intercalate "\n" $ ("# " ++) <$> L.lines c

tripleQuotedString :: String -> A.Expr
tripleQuotedString s = cst $ "\"\"\"" ++ s ++ "\"\"\"" -- TODO: escaping

unsupportedType :: String -> A.Expr
unsupportedType label = cst $ "[" ++ label ++ "]"

unsupportedVariant :: Show a => String -> a -> A.Expr
unsupportedVariant label obj = cst $ "[unsupported " ++ label ++ ": " ++ show obj ++ "]"
