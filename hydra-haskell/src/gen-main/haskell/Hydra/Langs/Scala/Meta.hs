-- | A Scala syntax model based on Scalameta (https://scalameta.org)

module Hydra.Langs.Scala.Meta where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype PredefString = 
  PredefString {
    unPredefString :: String}
  deriving (Eq, Ord, Read, Show)

_PredefString = (Core.Name "hydra/langs/scala/meta.PredefString")

data ScalaSymbol = 
  ScalaSymbol {
    scalaSymbolName :: String}
  deriving (Eq, Ord, Read, Show)

_ScalaSymbol = (Core.Name "hydra/langs/scala/meta.ScalaSymbol")

_ScalaSymbol_name = (Core.FieldName "name")

data Tree = 
  TreeRef Ref |
  TreeStat Stat |
  TreeType Type |
  TreeBounds Type_Bounds |
  TreePat Pat |
  TreeMember Member |
  TreeCtor Ctor |
  TreeTemplate Template |
  TreeMod Mod |
  TreeEnumerator Enumerator |
  TreeImporter Importer |
  TreeImportee Importee |
  TreeCaseTree CaseTree |
  TreeSource Source |
  TreeQuasi Quasi
  deriving (Eq, Ord, Read, Show)

_Tree = (Core.Name "hydra/langs/scala/meta.Tree")

_Tree_ref = (Core.FieldName "ref")

_Tree_stat = (Core.FieldName "stat")

_Tree_type = (Core.FieldName "type")

_Tree_bounds = (Core.FieldName "bounds")

_Tree_pat = (Core.FieldName "pat")

_Tree_member = (Core.FieldName "member")

_Tree_ctor = (Core.FieldName "ctor")

_Tree_template = (Core.FieldName "template")

_Tree_mod = (Core.FieldName "mod")

_Tree_enumerator = (Core.FieldName "enumerator")

_Tree_importer = (Core.FieldName "importer")

_Tree_importee = (Core.FieldName "importee")

_Tree_caseTree = (Core.FieldName "caseTree")

_Tree_source = (Core.FieldName "source")

_Tree_quasi = (Core.FieldName "quasi")

data Ref = 
  RefName Name |
  RefInit Init
  deriving (Eq, Ord, Read, Show)

_Ref = (Core.Name "hydra/langs/scala/meta.Ref")

_Ref_name = (Core.FieldName "name")

_Ref_init = (Core.FieldName "init")

data Stat = 
  StatTerm Data |
  StatDecl Decl |
  StatDefn Defn |
  StatImportExport ImportExportStat
  deriving (Eq, Ord, Read, Show)

_Stat = (Core.Name "hydra/langs/scala/meta.Stat")

_Stat_term = (Core.FieldName "term")

_Stat_decl = (Core.FieldName "decl")

_Stat_defn = (Core.FieldName "defn")

_Stat_importExport = (Core.FieldName "importExport")

data Name = 
  NameValue String |
  NameAnonymous  |
  NameIndeterminate PredefString
  deriving (Eq, Ord, Read, Show)

_Name = (Core.Name "hydra/langs/scala/meta.Name")

_Name_value = (Core.FieldName "value")

_Name_anonymous = (Core.FieldName "anonymous")

_Name_indeterminate = (Core.FieldName "indeterminate")

data Lit = 
  LitNull  |
  LitInt Int |
  LitDouble Double |
  LitFloat Float |
  LitByte Int8 |
  LitShort Int16 |
  LitChar Int |
  LitLong Int64 |
  LitBoolean Bool |
  LitUnit  |
  LitString String |
  LitSymbol ScalaSymbol
  deriving (Eq, Ord, Read, Show)

_Lit = (Core.Name "hydra/langs/scala/meta.Lit")

_Lit_null = (Core.FieldName "null")

_Lit_int = (Core.FieldName "int")

_Lit_double = (Core.FieldName "double")

_Lit_float = (Core.FieldName "float")

_Lit_byte = (Core.FieldName "byte")

_Lit_short = (Core.FieldName "short")

_Lit_char = (Core.FieldName "char")

_Lit_long = (Core.FieldName "long")

_Lit_boolean = (Core.FieldName "boolean")

_Lit_unit = (Core.FieldName "unit")

_Lit_string = (Core.FieldName "string")

_Lit_symbol = (Core.FieldName "symbol")

data Data = 
  DataLit Lit |
  DataRef Data_Ref |
  DataInterpolate Data_Interpolate |
  DataXml Data_Xml |
  DataApply Data_Apply |
  DataApplyUsing Data_ApplyUsing |
  DataApplyType Data_ApplyType |
  DataAssign Data_Assign |
  DataReturn Data_Return |
  DataThrow Data_Throw |
  DataAscribe Data_Ascribe |
  DataAnnotate Data_Annotate |
  DataTuple Data_Tuple |
  DataBlock Data_Block |
  DataEndMarker Data_EndMarker |
  DataIf Data_If |
  DataQuotedMacroExpr Data_QuotedMacroExpr |
  DataQuotedMacroType Data_QuotedMacroType |
  DataSplicedMacroExpr Data_SplicedMacroExpr |
  DataMatch Data_Match |
  DataTry Data_Try |
  DataTryWithHandler Data_TryWithHandler |
  DataFunctionData Data_FunctionData |
  DataPolyFunction Data_PolyFunction |
  DataPartialFunction Data_PartialFunction |
  DataWhile Data_While |
  DataDo Data_Do |
  DataFor Data_For |
  DataForYield Data_ForYield |
  DataNew Data_New |
  DataNewAnonymous Data_NewAnonymous |
  DataPlaceholder Data_Placeholder |
  DataEta Data_Eta |
  DataRepeated Data_Repeated |
  DataParam Data_Param
  deriving (Eq, Ord, Read, Show)

_Data = (Core.Name "hydra/langs/scala/meta.Data")

_Data_lit = (Core.FieldName "lit")

_Data_ref = (Core.FieldName "ref")

_Data_interpolate = (Core.FieldName "interpolate")

_Data_xml = (Core.FieldName "xml")

_Data_apply = (Core.FieldName "apply")

_Data_applyUsing = (Core.FieldName "applyUsing")

_Data_applyType = (Core.FieldName "applyType")

_Data_assign = (Core.FieldName "assign")

_Data_return = (Core.FieldName "return")

_Data_throw = (Core.FieldName "throw")

_Data_ascribe = (Core.FieldName "ascribe")

_Data_annotate = (Core.FieldName "annotate")

_Data_tuple = (Core.FieldName "tuple")

_Data_block = (Core.FieldName "block")

_Data_endMarker = (Core.FieldName "endMarker")

_Data_if = (Core.FieldName "if")

_Data_quotedMacroExpr = (Core.FieldName "quotedMacroExpr")

_Data_quotedMacroType = (Core.FieldName "quotedMacroType")

_Data_splicedMacroExpr = (Core.FieldName "splicedMacroExpr")

_Data_match = (Core.FieldName "match")

_Data_try = (Core.FieldName "try")

_Data_tryWithHandler = (Core.FieldName "tryWithHandler")

_Data_functionData = (Core.FieldName "functionData")

_Data_polyFunction = (Core.FieldName "polyFunction")

_Data_partialFunction = (Core.FieldName "partialFunction")

_Data_while = (Core.FieldName "while")

_Data_do = (Core.FieldName "do")

_Data_for = (Core.FieldName "for")

_Data_forYield = (Core.FieldName "forYield")

_Data_new = (Core.FieldName "new")

_Data_newAnonymous = (Core.FieldName "newAnonymous")

_Data_placeholder = (Core.FieldName "placeholder")

_Data_eta = (Core.FieldName "eta")

_Data_repeated = (Core.FieldName "repeated")

_Data_param = (Core.FieldName "param")

data Data_Ref = 
  Data_RefThis Data_This |
  Data_RefSuper Data_Super |
  Data_RefName Data_Name |
  Data_RefAnonymous Data_Anonymous |
  Data_RefSelect Data_Select |
  Data_RefApplyUnary Data_ApplyUnary
  deriving (Eq, Ord, Read, Show)

_Data_Ref = (Core.Name "hydra/langs/scala/meta.Data.Ref")

_Data_Ref_this = (Core.FieldName "this")

_Data_Ref_super = (Core.FieldName "super")

_Data_Ref_name = (Core.FieldName "name")

_Data_Ref_anonymous = (Core.FieldName "anonymous")

_Data_Ref_select = (Core.FieldName "select")

_Data_Ref_applyUnary = (Core.FieldName "applyUnary")

data Data_This = 
  Data_This {}
  deriving (Eq, Ord, Read, Show)

_Data_This = (Core.Name "hydra/langs/scala/meta.Data.This")

data Data_Super = 
  Data_Super {
    data_SuperThisp :: Name,
    data_SuperSuperp :: Name}
  deriving (Eq, Ord, Read, Show)

_Data_Super = (Core.Name "hydra/langs/scala/meta.Data.Super")

_Data_Super_thisp = (Core.FieldName "thisp")

_Data_Super_superp = (Core.FieldName "superp")

data Data_Name = 
  Data_Name {
    data_NameValue :: PredefString}
  deriving (Eq, Ord, Read, Show)

_Data_Name = (Core.Name "hydra/langs/scala/meta.Data.Name")

_Data_Name_value = (Core.FieldName "value")

data Data_Anonymous = 
  Data_Anonymous {}
  deriving (Eq, Ord, Read, Show)

_Data_Anonymous = (Core.Name "hydra/langs/scala/meta.Data.Anonymous")

data Data_Select = 
  Data_Select {
    data_SelectQual :: Data,
    data_SelectName :: Data_Name}
  deriving (Eq, Ord, Read, Show)

_Data_Select = (Core.Name "hydra/langs/scala/meta.Data.Select")

_Data_Select_qual = (Core.FieldName "qual")

_Data_Select_name = (Core.FieldName "name")

data Data_Interpolate = 
  Data_Interpolate {
    data_InterpolatePrefix :: Data_Name,
    data_InterpolateParts :: [Lit],
    data_InterpolateArgs :: [Data]}
  deriving (Eq, Ord, Read, Show)

_Data_Interpolate = (Core.Name "hydra/langs/scala/meta.Data.Interpolate")

_Data_Interpolate_prefix = (Core.FieldName "prefix")

_Data_Interpolate_parts = (Core.FieldName "parts")

_Data_Interpolate_args = (Core.FieldName "args")

data Data_Xml = 
  Data_Xml {
    data_XmlParts :: [Lit],
    data_XmlArgs :: [Data]}
  deriving (Eq, Ord, Read, Show)

_Data_Xml = (Core.Name "hydra/langs/scala/meta.Data.Xml")

_Data_Xml_parts = (Core.FieldName "parts")

_Data_Xml_args = (Core.FieldName "args")

data Data_Apply = 
  Data_Apply {
    data_ApplyFun :: Data,
    data_ApplyArgs :: [Data]}
  deriving (Eq, Ord, Read, Show)

_Data_Apply = (Core.Name "hydra/langs/scala/meta.Data.Apply")

_Data_Apply_fun = (Core.FieldName "fun")

_Data_Apply_args = (Core.FieldName "args")

data Data_ApplyUsing = 
  Data_ApplyUsing {
    data_ApplyUsingFun :: Data,
    data_ApplyUsingTargs :: [Data]}
  deriving (Eq, Ord, Read, Show)

_Data_ApplyUsing = (Core.Name "hydra/langs/scala/meta.Data.ApplyUsing")

_Data_ApplyUsing_fun = (Core.FieldName "fun")

_Data_ApplyUsing_targs = (Core.FieldName "targs")

data Data_ApplyType = 
  Data_ApplyType {
    data_ApplyTypeLhs :: Data,
    data_ApplyTypeOp :: Data_Name,
    data_ApplyTypeTargs :: [Type],
    data_ApplyTypeArgs :: [Data]}
  deriving (Eq, Ord, Read, Show)

_Data_ApplyType = (Core.Name "hydra/langs/scala/meta.Data.ApplyType")

_Data_ApplyType_lhs = (Core.FieldName "lhs")

_Data_ApplyType_op = (Core.FieldName "op")

_Data_ApplyType_targs = (Core.FieldName "targs")

_Data_ApplyType_args = (Core.FieldName "args")

data Data_ApplyInfix = 
  Data_ApplyInfix {
    data_ApplyInfixLhs :: Data,
    data_ApplyInfixOp :: Data_Name,
    data_ApplyInfixTargs :: [Type],
    data_ApplyInfixArgs :: [Data]}
  deriving (Eq, Ord, Read, Show)

_Data_ApplyInfix = (Core.Name "hydra/langs/scala/meta.Data.ApplyInfix")

_Data_ApplyInfix_lhs = (Core.FieldName "lhs")

_Data_ApplyInfix_op = (Core.FieldName "op")

_Data_ApplyInfix_targs = (Core.FieldName "targs")

_Data_ApplyInfix_args = (Core.FieldName "args")

data Data_ApplyUnary = 
  Data_ApplyUnary {
    data_ApplyUnaryOp :: Data_Name,
    data_ApplyUnaryArg :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_ApplyUnary = (Core.Name "hydra/langs/scala/meta.Data.ApplyUnary")

_Data_ApplyUnary_op = (Core.FieldName "op")

_Data_ApplyUnary_arg = (Core.FieldName "arg")

data Data_Assign = 
  Data_Assign {
    data_AssignLhs :: Data,
    data_AssignRhs :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_Assign = (Core.Name "hydra/langs/scala/meta.Data.Assign")

_Data_Assign_lhs = (Core.FieldName "lhs")

_Data_Assign_rhs = (Core.FieldName "rhs")

data Data_Return = 
  Data_Return {
    data_ReturnExpr :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_Return = (Core.Name "hydra/langs/scala/meta.Data.Return")

_Data_Return_expr = (Core.FieldName "expr")

data Data_Throw = 
  Data_Throw {
    data_ThrowExpr :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_Throw = (Core.Name "hydra/langs/scala/meta.Data.Throw")

_Data_Throw_expr = (Core.FieldName "expr")

data Data_Ascribe = 
  Data_Ascribe {
    data_AscribeExpr :: Data,
    data_AscribeTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Data_Ascribe = (Core.Name "hydra/langs/scala/meta.Data.Ascribe")

_Data_Ascribe_expr = (Core.FieldName "expr")

_Data_Ascribe_tpe = (Core.FieldName "tpe")

data Data_Annotate = 
  Data_Annotate {
    data_AnnotateExpr :: Data,
    data_AnnotateAnnots :: [Mod_Annot]}
  deriving (Eq, Ord, Read, Show)

_Data_Annotate = (Core.Name "hydra/langs/scala/meta.Data.Annotate")

_Data_Annotate_expr = (Core.FieldName "expr")

_Data_Annotate_annots = (Core.FieldName "annots")

data Data_Tuple = 
  Data_Tuple {
    data_TupleArgs :: [Data]}
  deriving (Eq, Ord, Read, Show)

_Data_Tuple = (Core.Name "hydra/langs/scala/meta.Data.Tuple")

_Data_Tuple_args = (Core.FieldName "args")

data Data_Block = 
  Data_Block {
    data_BlockStats :: [Stat]}
  deriving (Eq, Ord, Read, Show)

_Data_Block = (Core.Name "hydra/langs/scala/meta.Data.Block")

_Data_Block_stats = (Core.FieldName "stats")

data Data_EndMarker = 
  Data_EndMarker {
    data_EndMarkerName :: Data_Name}
  deriving (Eq, Ord, Read, Show)

_Data_EndMarker = (Core.Name "hydra/langs/scala/meta.Data.EndMarker")

_Data_EndMarker_name = (Core.FieldName "name")

data Data_If = 
  Data_If {
    data_IfCond :: Data,
    data_IfThenp :: Data,
    data_IfElsep :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_If = (Core.Name "hydra/langs/scala/meta.Data.If")

_Data_If_cond = (Core.FieldName "cond")

_Data_If_thenp = (Core.FieldName "thenp")

_Data_If_elsep = (Core.FieldName "elsep")

data Data_QuotedMacroExpr = 
  Data_QuotedMacroExpr {
    data_QuotedMacroExprBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_QuotedMacroExpr = (Core.Name "hydra/langs/scala/meta.Data.QuotedMacroExpr")

_Data_QuotedMacroExpr_body = (Core.FieldName "body")

data Data_QuotedMacroType = 
  Data_QuotedMacroType {
    data_QuotedMacroTypeTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Data_QuotedMacroType = (Core.Name "hydra/langs/scala/meta.Data.QuotedMacroType")

_Data_QuotedMacroType_tpe = (Core.FieldName "tpe")

data Data_SplicedMacroExpr = 
  Data_SplicedMacroExpr {
    data_SplicedMacroExprBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_SplicedMacroExpr = (Core.Name "hydra/langs/scala/meta.Data.SplicedMacroExpr")

_Data_SplicedMacroExpr_body = (Core.FieldName "body")

data Data_Match = 
  Data_Match {
    data_MatchExpr :: Data,
    data_MatchCases :: [Case]}
  deriving (Eq, Ord, Read, Show)

_Data_Match = (Core.Name "hydra/langs/scala/meta.Data.Match")

_Data_Match_expr = (Core.FieldName "expr")

_Data_Match_cases = (Core.FieldName "cases")

data Data_Try = 
  Data_Try {
    data_TryExpr :: Data,
    data_TryCatchp :: [Case],
    data_TryFinallyp :: (Maybe Data)}
  deriving (Eq, Ord, Read, Show)

_Data_Try = (Core.Name "hydra/langs/scala/meta.Data.Try")

_Data_Try_expr = (Core.FieldName "expr")

_Data_Try_catchp = (Core.FieldName "catchp")

_Data_Try_finallyp = (Core.FieldName "finallyp")

data Data_TryWithHandler = 
  Data_TryWithHandler {
    data_TryWithHandlerExpr :: Data,
    data_TryWithHandlerCatchp :: Data,
    data_TryWithHandlerFinallyp :: (Maybe Data)}
  deriving (Eq, Ord, Read, Show)

_Data_TryWithHandler = (Core.Name "hydra/langs/scala/meta.Data.TryWithHandler")

_Data_TryWithHandler_expr = (Core.FieldName "expr")

_Data_TryWithHandler_catchp = (Core.FieldName "catchp")

_Data_TryWithHandler_finallyp = (Core.FieldName "finallyp")

data Data_FunctionData = 
  Data_FunctionDataContextFunction Data_ContextFunction |
  Data_FunctionDataFunction Data_Function
  deriving (Eq, Ord, Read, Show)

_Data_FunctionData = (Core.Name "hydra/langs/scala/meta.Data.FunctionData")

_Data_FunctionData_contextFunction = (Core.FieldName "contextFunction")

_Data_FunctionData_function = (Core.FieldName "function")

data Data_ContextFunction = 
  Data_ContextFunction {
    data_ContextFunctionParams :: [Data_Param],
    data_ContextFunctionBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_ContextFunction = (Core.Name "hydra/langs/scala/meta.Data.ContextFunction")

_Data_ContextFunction_params = (Core.FieldName "params")

_Data_ContextFunction_body = (Core.FieldName "body")

data Data_Function = 
  Data_Function {
    data_FunctionParams :: [Data_Param],
    data_FunctionBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_Function = (Core.Name "hydra/langs/scala/meta.Data.Function")

_Data_Function_params = (Core.FieldName "params")

_Data_Function_body = (Core.FieldName "body")

data Data_PolyFunction = 
  Data_PolyFunction {
    data_PolyFunctionTparams :: [Type_Param],
    data_PolyFunctionBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_PolyFunction = (Core.Name "hydra/langs/scala/meta.Data.PolyFunction")

_Data_PolyFunction_tparams = (Core.FieldName "tparams")

_Data_PolyFunction_body = (Core.FieldName "body")

data Data_PartialFunction = 
  Data_PartialFunction {
    data_PartialFunctionCases :: [Case]}
  deriving (Eq, Ord, Read, Show)

_Data_PartialFunction = (Core.Name "hydra/langs/scala/meta.Data.PartialFunction")

_Data_PartialFunction_cases = (Core.FieldName "cases")

data Data_While = 
  Data_While {
    data_WhileExpr :: Data,
    data_WhileBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_While = (Core.Name "hydra/langs/scala/meta.Data.While")

_Data_While_expr = (Core.FieldName "expr")

_Data_While_body = (Core.FieldName "body")

data Data_Do = 
  Data_Do {
    data_DoBody :: Data,
    data_DoExpr :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_Do = (Core.Name "hydra/langs/scala/meta.Data.Do")

_Data_Do_body = (Core.FieldName "body")

_Data_Do_expr = (Core.FieldName "expr")

data Data_For = 
  Data_For {
    data_ForEnums :: [Enumerator]}
  deriving (Eq, Ord, Read, Show)

_Data_For = (Core.Name "hydra/langs/scala/meta.Data.For")

_Data_For_enums = (Core.FieldName "enums")

data Data_ForYield = 
  Data_ForYield {
    data_ForYieldEnums :: [Enumerator]}
  deriving (Eq, Ord, Read, Show)

_Data_ForYield = (Core.Name "hydra/langs/scala/meta.Data.ForYield")

_Data_ForYield_enums = (Core.FieldName "enums")

data Data_New = 
  Data_New {
    data_NewInit :: Init}
  deriving (Eq, Ord, Read, Show)

_Data_New = (Core.Name "hydra/langs/scala/meta.Data.New")

_Data_New_init = (Core.FieldName "init")

data Data_NewAnonymous = 
  Data_NewAnonymous {
    data_NewAnonymousTempl :: Template}
  deriving (Eq, Ord, Read, Show)

_Data_NewAnonymous = (Core.Name "hydra/langs/scala/meta.Data.NewAnonymous")

_Data_NewAnonymous_templ = (Core.FieldName "templ")

data Data_Placeholder = 
  Data_Placeholder {}
  deriving (Eq, Ord, Read, Show)

_Data_Placeholder = (Core.Name "hydra/langs/scala/meta.Data.Placeholder")

data Data_Eta = 
  Data_Eta {
    data_EtaExpr :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_Eta = (Core.Name "hydra/langs/scala/meta.Data.Eta")

_Data_Eta_expr = (Core.FieldName "expr")

data Data_Repeated = 
  Data_Repeated {
    data_RepeatedExpr :: Data}
  deriving (Eq, Ord, Read, Show)

_Data_Repeated = (Core.Name "hydra/langs/scala/meta.Data.Repeated")

_Data_Repeated_expr = (Core.FieldName "expr")

data Data_Param = 
  Data_Param {
    data_ParamMods :: [Mod],
    data_ParamName :: Name,
    data_ParamDecltpe :: (Maybe Type),
    data_ParamDefault :: (Maybe Data)}
  deriving (Eq, Ord, Read, Show)

_Data_Param = (Core.Name "hydra/langs/scala/meta.Data.Param")

_Data_Param_mods = (Core.FieldName "mods")

_Data_Param_name = (Core.FieldName "name")

_Data_Param_decltpe = (Core.FieldName "decltpe")

_Data_Param_default = (Core.FieldName "default")

data Type = 
  TypeRef Type_Ref |
  TypeAnonymousName Type_AnonymousName |
  TypeApply Type_Apply |
  TypeApplyInfix Type_ApplyInfix |
  TypeFunctionType Type_FunctionType |
  TypePolyFunction Type_PolyFunction |
  TypeImplicitFunction Type_ImplicitFunction |
  TypeTuple Type_Tuple |
  TypeWith Type_With |
  TypeAnd Type_And |
  TypeOr Type_Or |
  TypeRefine Type_Refine |
  TypeExistential Type_Existential |
  TypeAnnotate Type_Annotate |
  TypeLambda Type_Lambda |
  TypeMacro Type_Macro |
  TypeMethod Type_Method |
  TypePlaceholder Type_Placeholder |
  TypeByName Type_ByName |
  TypeRepeated Type_Repeated |
  TypeVar Type_Var |
  TypeTypedParam Type_TypedParam |
  TypeMatch Type_Match
  deriving (Eq, Ord, Read, Show)

_Type = (Core.Name "hydra/langs/scala/meta.Type")

_Type_ref = (Core.FieldName "ref")

_Type_anonymousName = (Core.FieldName "anonymousName")

_Type_apply = (Core.FieldName "apply")

_Type_applyInfix = (Core.FieldName "applyInfix")

_Type_functionType = (Core.FieldName "functionType")

_Type_polyFunction = (Core.FieldName "polyFunction")

_Type_implicitFunction = (Core.FieldName "implicitFunction")

_Type_tuple = (Core.FieldName "tuple")

_Type_with = (Core.FieldName "with")

_Type_and = (Core.FieldName "and")

_Type_or = (Core.FieldName "or")

_Type_refine = (Core.FieldName "refine")

_Type_existential = (Core.FieldName "existential")

_Type_annotate = (Core.FieldName "annotate")

_Type_lambda = (Core.FieldName "lambda")

_Type_macro = (Core.FieldName "macro")

_Type_method = (Core.FieldName "method")

_Type_placeholder = (Core.FieldName "placeholder")

_Type_byName = (Core.FieldName "byName")

_Type_repeated = (Core.FieldName "repeated")

_Type_var = (Core.FieldName "var")

_Type_typedParam = (Core.FieldName "typedParam")

_Type_match = (Core.FieldName "match")

data Type_Ref = 
  Type_RefName Type_Name |
  Type_RefSelect Type_Select |
  Type_RefProject Type_Project |
  Type_RefSingleton Type_Singleton
  deriving (Eq, Ord, Read, Show)

_Type_Ref = (Core.Name "hydra/langs/scala/meta.Type.Ref")

_Type_Ref_name = (Core.FieldName "name")

_Type_Ref_select = (Core.FieldName "select")

_Type_Ref_project = (Core.FieldName "project")

_Type_Ref_singleton = (Core.FieldName "singleton")

data Type_Name = 
  Type_Name {
    type_NameValue :: String}
  deriving (Eq, Ord, Read, Show)

_Type_Name = (Core.Name "hydra/langs/scala/meta.Type.Name")

_Type_Name_value = (Core.FieldName "value")

data Type_AnonymousName = 
  Type_AnonymousName {}
  deriving (Eq, Ord, Read, Show)

_Type_AnonymousName = (Core.Name "hydra/langs/scala/meta.Type.AnonymousName")

data Type_Select = 
  Type_Select {
    type_SelectQual :: Data_Ref,
    type_SelectName :: Type_Name}
  deriving (Eq, Ord, Read, Show)

_Type_Select = (Core.Name "hydra/langs/scala/meta.Type.Select")

_Type_Select_qual = (Core.FieldName "qual")

_Type_Select_name = (Core.FieldName "name")

data Type_Project = 
  Type_Project {
    type_ProjectQual :: Type,
    type_ProjectName :: Type_Name}
  deriving (Eq, Ord, Read, Show)

_Type_Project = (Core.Name "hydra/langs/scala/meta.Type.Project")

_Type_Project_qual = (Core.FieldName "qual")

_Type_Project_name = (Core.FieldName "name")

data Type_Singleton = 
  Type_Singleton {
    type_SingletonRef :: Data_Ref}
  deriving (Eq, Ord, Read, Show)

_Type_Singleton = (Core.Name "hydra/langs/scala/meta.Type.Singleton")

_Type_Singleton_ref = (Core.FieldName "ref")

data Type_Apply = 
  Type_Apply {
    type_ApplyTpe :: Type,
    type_ApplyArgs :: [Type]}
  deriving (Eq, Ord, Read, Show)

_Type_Apply = (Core.Name "hydra/langs/scala/meta.Type.Apply")

_Type_Apply_tpe = (Core.FieldName "tpe")

_Type_Apply_args = (Core.FieldName "args")

data Type_ApplyInfix = 
  Type_ApplyInfix {
    type_ApplyInfixLhs :: Type,
    type_ApplyInfixOp :: Type_Name,
    type_ApplyInfixRhs :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_ApplyInfix = (Core.Name "hydra/langs/scala/meta.Type.ApplyInfix")

_Type_ApplyInfix_lhs = (Core.FieldName "lhs")

_Type_ApplyInfix_op = (Core.FieldName "op")

_Type_ApplyInfix_rhs = (Core.FieldName "rhs")

data Type_FunctionType = 
  Type_FunctionTypeFunction Type_Function |
  Type_FunctionTypeContextFunction Type_ContextFunction
  deriving (Eq, Ord, Read, Show)

_Type_FunctionType = (Core.Name "hydra/langs/scala/meta.Type.FunctionType")

_Type_FunctionType_function = (Core.FieldName "function")

_Type_FunctionType_contextFunction = (Core.FieldName "contextFunction")

data Type_Function = 
  Type_Function {
    type_FunctionParams :: [Type],
    type_FunctionRes :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Function = (Core.Name "hydra/langs/scala/meta.Type.Function")

_Type_Function_params = (Core.FieldName "params")

_Type_Function_res = (Core.FieldName "res")

data Type_PolyFunction = 
  Type_PolyFunction {
    type_PolyFunctionTparams :: [Type_Param],
    type_PolyFunctionTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_PolyFunction = (Core.Name "hydra/langs/scala/meta.Type.PolyFunction")

_Type_PolyFunction_tparams = (Core.FieldName "tparams")

_Type_PolyFunction_tpe = (Core.FieldName "tpe")

data Type_ContextFunction = 
  Type_ContextFunction {
    type_ContextFunctionParams :: [Type],
    type_ContextFunctionRes :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_ContextFunction = (Core.Name "hydra/langs/scala/meta.Type.ContextFunction")

_Type_ContextFunction_params = (Core.FieldName "params")

_Type_ContextFunction_res = (Core.FieldName "res")

data Type_ImplicitFunction = 
  Type_ImplicitFunction {
    type_ImplicitFunctionParams :: [Type],
    type_ImplicitFunctionRes :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_ImplicitFunction = (Core.Name "hydra/langs/scala/meta.Type.ImplicitFunction")

_Type_ImplicitFunction_params = (Core.FieldName "params")

_Type_ImplicitFunction_res = (Core.FieldName "res")

data Type_Tuple = 
  Type_Tuple {
    type_TupleArgs :: [Type]}
  deriving (Eq, Ord, Read, Show)

_Type_Tuple = (Core.Name "hydra/langs/scala/meta.Type.Tuple")

_Type_Tuple_args = (Core.FieldName "args")

data Type_With = 
  Type_With {
    type_WithLhs :: Type,
    type_WithRhs :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_With = (Core.Name "hydra/langs/scala/meta.Type.With")

_Type_With_lhs = (Core.FieldName "lhs")

_Type_With_rhs = (Core.FieldName "rhs")

data Type_And = 
  Type_And {
    type_AndLhs :: Type,
    type_AndRhs :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_And = (Core.Name "hydra/langs/scala/meta.Type.And")

_Type_And_lhs = (Core.FieldName "lhs")

_Type_And_rhs = (Core.FieldName "rhs")

data Type_Or = 
  Type_Or {
    type_OrLhs :: Type,
    type_OrRhs :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Or = (Core.Name "hydra/langs/scala/meta.Type.Or")

_Type_Or_lhs = (Core.FieldName "lhs")

_Type_Or_rhs = (Core.FieldName "rhs")

data Type_Refine = 
  Type_Refine {
    type_RefineTpe :: (Maybe Type),
    type_RefineStats :: [Stat]}
  deriving (Eq, Ord, Read, Show)

_Type_Refine = (Core.Name "hydra/langs/scala/meta.Type.Refine")

_Type_Refine_tpe = (Core.FieldName "tpe")

_Type_Refine_stats = (Core.FieldName "stats")

data Type_Existential = 
  Type_Existential {
    type_ExistentialTpe :: Type,
    type_ExistentialStats :: [Stat]}
  deriving (Eq, Ord, Read, Show)

_Type_Existential = (Core.Name "hydra/langs/scala/meta.Type.Existential")

_Type_Existential_tpe = (Core.FieldName "tpe")

_Type_Existential_stats = (Core.FieldName "stats")

data Type_Annotate = 
  Type_Annotate {
    type_AnnotateTpe :: Type,
    type_AnnotateAnnots :: [Mod_Annot]}
  deriving (Eq, Ord, Read, Show)

_Type_Annotate = (Core.Name "hydra/langs/scala/meta.Type.Annotate")

_Type_Annotate_tpe = (Core.FieldName "tpe")

_Type_Annotate_annots = (Core.FieldName "annots")

data Type_Lambda = 
  Type_Lambda {
    type_LambdaTparams :: [Type_Param],
    type_LambdaTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Lambda = (Core.Name "hydra/langs/scala/meta.Type.Lambda")

_Type_Lambda_tparams = (Core.FieldName "tparams")

_Type_Lambda_tpe = (Core.FieldName "tpe")

data Type_Macro = 
  Type_Macro {
    type_MacroBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Type_Macro = (Core.Name "hydra/langs/scala/meta.Type.Macro")

_Type_Macro_body = (Core.FieldName "body")

data Type_Method = 
  Type_Method {
    type_MethodParamss :: [[Data_Param]],
    type_MethodTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Method = (Core.Name "hydra/langs/scala/meta.Type.Method")

_Type_Method_paramss = (Core.FieldName "paramss")

_Type_Method_tpe = (Core.FieldName "tpe")

data Type_Placeholder = 
  Type_Placeholder {
    type_PlaceholderBounds :: Type_Bounds}
  deriving (Eq, Ord, Read, Show)

_Type_Placeholder = (Core.Name "hydra/langs/scala/meta.Type.Placeholder")

_Type_Placeholder_bounds = (Core.FieldName "bounds")

data Type_Bounds = 
  Type_Bounds {
    type_BoundsLo :: (Maybe Type),
    type_BoundsHi :: (Maybe Type)}
  deriving (Eq, Ord, Read, Show)

_Type_Bounds = (Core.Name "hydra/langs/scala/meta.Type.Bounds")

_Type_Bounds_lo = (Core.FieldName "lo")

_Type_Bounds_hi = (Core.FieldName "hi")

data Type_ByName = 
  Type_ByName {
    type_ByNameTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_ByName = (Core.Name "hydra/langs/scala/meta.Type.ByName")

_Type_ByName_tpe = (Core.FieldName "tpe")

data Type_Repeated = 
  Type_Repeated {
    type_RepeatedTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_Repeated = (Core.Name "hydra/langs/scala/meta.Type.Repeated")

_Type_Repeated_tpe = (Core.FieldName "tpe")

data Type_Var = 
  Type_Var {
    type_VarName :: Type_Name}
  deriving (Eq, Ord, Read, Show)

_Type_Var = (Core.Name "hydra/langs/scala/meta.Type.Var")

_Type_Var_name = (Core.FieldName "name")

data Type_TypedParam = 
  Type_TypedParam {
    type_TypedParamName :: Name,
    type_TypedParamTyp :: Type}
  deriving (Eq, Ord, Read, Show)

_Type_TypedParam = (Core.Name "hydra/langs/scala/meta.Type.TypedParam")

_Type_TypedParam_name = (Core.FieldName "name")

_Type_TypedParam_typ = (Core.FieldName "typ")

data Type_Param = 
  Type_Param {
    type_ParamMods :: [Mod],
    type_ParamName :: Name,
    type_ParamTparams :: [Type_Param],
    type_ParamTbounds :: [Type_Bounds],
    type_ParamVbounds :: [Type],
    type_ParamCbounds :: [Type]}
  deriving (Eq, Ord, Read, Show)

_Type_Param = (Core.Name "hydra/langs/scala/meta.Type.Param")

_Type_Param_mods = (Core.FieldName "mods")

_Type_Param_name = (Core.FieldName "name")

_Type_Param_tparams = (Core.FieldName "tparams")

_Type_Param_tbounds = (Core.FieldName "tbounds")

_Type_Param_vbounds = (Core.FieldName "vbounds")

_Type_Param_cbounds = (Core.FieldName "cbounds")

data Type_Match = 
  Type_Match {
    type_MatchTpe :: Type,
    type_MatchCases :: [TypeCase]}
  deriving (Eq, Ord, Read, Show)

_Type_Match = (Core.Name "hydra/langs/scala/meta.Type.Match")

_Type_Match_tpe = (Core.FieldName "tpe")

_Type_Match_cases = (Core.FieldName "cases")

data Pat = 
  PatVar Pat_Var |
  PatWildcard  |
  PatSeqWildcard  |
  PatBind Pat_Bind |
  PatAlternative Pat_Alternative |
  PatTuple Pat_Tuple |
  PatRepeated Pat_Repeated |
  PatExtract Pat_Extract |
  PatExtractInfix Pat_ExtractInfix |
  PatInterpolate Pat_Interpolate |
  PatXml Pat_Xml |
  PatTyped Pat_Typed |
  PatMacro Pat_Macro |
  PatGiven Pat_Given
  deriving (Eq, Ord, Read, Show)

_Pat = (Core.Name "hydra/langs/scala/meta.Pat")

_Pat_var = (Core.FieldName "var")

_Pat_wildcard = (Core.FieldName "wildcard")

_Pat_seqWildcard = (Core.FieldName "seqWildcard")

_Pat_bind = (Core.FieldName "bind")

_Pat_alternative = (Core.FieldName "alternative")

_Pat_tuple = (Core.FieldName "tuple")

_Pat_repeated = (Core.FieldName "repeated")

_Pat_extract = (Core.FieldName "extract")

_Pat_extractInfix = (Core.FieldName "extractInfix")

_Pat_interpolate = (Core.FieldName "interpolate")

_Pat_xml = (Core.FieldName "xml")

_Pat_typed = (Core.FieldName "typed")

_Pat_macro = (Core.FieldName "macro")

_Pat_given = (Core.FieldName "given")

data Pat_Var = 
  Pat_Var {
    pat_VarName :: Data_Name}
  deriving (Eq, Ord, Read, Show)

_Pat_Var = (Core.Name "hydra/langs/scala/meta.Pat.Var")

_Pat_Var_name = (Core.FieldName "name")

data Pat_Bind = 
  Pat_Bind {
    pat_BindLhs :: Pat,
    pat_BindRhs :: Pat}
  deriving (Eq, Ord, Read, Show)

_Pat_Bind = (Core.Name "hydra/langs/scala/meta.Pat.Bind")

_Pat_Bind_lhs = (Core.FieldName "lhs")

_Pat_Bind_rhs = (Core.FieldName "rhs")

data Pat_Alternative = 
  Pat_Alternative {
    pat_AlternativeLhs :: Pat,
    pat_AlternativeRhs :: Pat}
  deriving (Eq, Ord, Read, Show)

_Pat_Alternative = (Core.Name "hydra/langs/scala/meta.Pat.Alternative")

_Pat_Alternative_lhs = (Core.FieldName "lhs")

_Pat_Alternative_rhs = (Core.FieldName "rhs")

data Pat_Tuple = 
  Pat_Tuple {
    pat_TupleArgs :: [Pat]}
  deriving (Eq, Ord, Read, Show)

_Pat_Tuple = (Core.Name "hydra/langs/scala/meta.Pat.Tuple")

_Pat_Tuple_args = (Core.FieldName "args")

data Pat_Repeated = 
  Pat_Repeated {
    pat_RepeatedName :: Data_Name}
  deriving (Eq, Ord, Read, Show)

_Pat_Repeated = (Core.Name "hydra/langs/scala/meta.Pat.Repeated")

_Pat_Repeated_name = (Core.FieldName "name")

data Pat_Extract = 
  Pat_Extract {
    pat_ExtractFun :: Data,
    pat_ExtractArgs :: [Pat]}
  deriving (Eq, Ord, Read, Show)

_Pat_Extract = (Core.Name "hydra/langs/scala/meta.Pat.Extract")

_Pat_Extract_fun = (Core.FieldName "fun")

_Pat_Extract_args = (Core.FieldName "args")

data Pat_ExtractInfix = 
  Pat_ExtractInfix {
    pat_ExtractInfixLhs :: Pat,
    pat_ExtractInfixOp :: Data_Name,
    pat_ExtractInfixRhs :: [Pat]}
  deriving (Eq, Ord, Read, Show)

_Pat_ExtractInfix = (Core.Name "hydra/langs/scala/meta.Pat.ExtractInfix")

_Pat_ExtractInfix_lhs = (Core.FieldName "lhs")

_Pat_ExtractInfix_op = (Core.FieldName "op")

_Pat_ExtractInfix_rhs = (Core.FieldName "rhs")

data Pat_Interpolate = 
  Pat_Interpolate {
    pat_InterpolatePrefix :: Data_Name,
    pat_InterpolateParts :: [Lit]}
  deriving (Eq, Ord, Read, Show)

_Pat_Interpolate = (Core.Name "hydra/langs/scala/meta.Pat.Interpolate")

_Pat_Interpolate_prefix = (Core.FieldName "prefix")

_Pat_Interpolate_parts = (Core.FieldName "parts")

data Pat_Xml = 
  Pat_Xml {
    pat_XmlParts :: [Lit],
    pat_XmlArgs :: [Pat]}
  deriving (Eq, Ord, Read, Show)

_Pat_Xml = (Core.Name "hydra/langs/scala/meta.Pat.Xml")

_Pat_Xml_parts = (Core.FieldName "parts")

_Pat_Xml_args = (Core.FieldName "args")

data Pat_Typed = 
  Pat_Typed {
    pat_TypedLhs :: Pat,
    pat_TypedRhs :: Type}
  deriving (Eq, Ord, Read, Show)

_Pat_Typed = (Core.Name "hydra/langs/scala/meta.Pat.Typed")

_Pat_Typed_lhs = (Core.FieldName "lhs")

_Pat_Typed_rhs = (Core.FieldName "rhs")

data Pat_Macro = 
  Pat_Macro {
    pat_MacroBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Pat_Macro = (Core.Name "hydra/langs/scala/meta.Pat.Macro")

_Pat_Macro_body = (Core.FieldName "body")

data Pat_Given = 
  Pat_Given {
    pat_GivenTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Pat_Given = (Core.Name "hydra/langs/scala/meta.Pat.Given")

_Pat_Given_tpe = (Core.FieldName "tpe")

data Member = 
  MemberTerm Member_Data |
  MemberType Member_Type |
  MemberTermParam Data_Param |
  MemberTypeParam Type_Param |
  MemberSelf Self
  deriving (Eq, Ord, Read, Show)

_Member = (Core.Name "hydra/langs/scala/meta.Member")

_Member_term = (Core.FieldName "term")

_Member_type = (Core.FieldName "type")

_Member_termParam = (Core.FieldName "termParam")

_Member_typeParam = (Core.FieldName "typeParam")

_Member_self = (Core.FieldName "self")

data Member_Data = 
  Member_DataPkg Pkg |
  Member_DataObject Pkg_Object
  deriving (Eq, Ord, Read, Show)

_Member_Data = (Core.Name "hydra/langs/scala/meta.Member.Data")

_Member_Data_pkg = (Core.FieldName "pkg")

_Member_Data_object = (Core.FieldName "object")

data Member_Type = 
  Member_Type {
    member_TypeName :: Type_Name}
  deriving (Eq, Ord, Read, Show)

_Member_Type = (Core.Name "hydra/langs/scala/meta.Member.Type")

_Member_Type_name = (Core.FieldName "name")

data Decl = 
  DeclVal Decl_Val |
  DeclVar Decl_Var |
  DeclDef Decl_Def |
  DeclType Decl_Type |
  DeclGiven Decl_Given
  deriving (Eq, Ord, Read, Show)

_Decl = (Core.Name "hydra/langs/scala/meta.Decl")

_Decl_val = (Core.FieldName "val")

_Decl_var = (Core.FieldName "var")

_Decl_def = (Core.FieldName "def")

_Decl_type = (Core.FieldName "type")

_Decl_given = (Core.FieldName "given")

data Decl_Val = 
  Decl_Val {
    decl_ValMods :: [Mod],
    decl_ValPats :: [Pat],
    decl_ValDecltpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Decl_Val = (Core.Name "hydra/langs/scala/meta.Decl.Val")

_Decl_Val_mods = (Core.FieldName "mods")

_Decl_Val_pats = (Core.FieldName "pats")

_Decl_Val_decltpe = (Core.FieldName "decltpe")

data Decl_Var = 
  Decl_Var {
    decl_VarMods :: [Mod],
    decl_VarPats :: [Pat],
    decl_VarDecltpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Decl_Var = (Core.Name "hydra/langs/scala/meta.Decl.Var")

_Decl_Var_mods = (Core.FieldName "mods")

_Decl_Var_pats = (Core.FieldName "pats")

_Decl_Var_decltpe = (Core.FieldName "decltpe")

data Decl_Def = 
  Decl_Def {
    decl_DefMods :: [Mod],
    decl_DefName :: Data_Name,
    decl_DefTparams :: [Type_Param],
    decl_DefParamss :: [[Data_Param]],
    decl_DefDecltpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Decl_Def = (Core.Name "hydra/langs/scala/meta.Decl.Def")

_Decl_Def_mods = (Core.FieldName "mods")

_Decl_Def_name = (Core.FieldName "name")

_Decl_Def_tparams = (Core.FieldName "tparams")

_Decl_Def_paramss = (Core.FieldName "paramss")

_Decl_Def_decltpe = (Core.FieldName "decltpe")

data Decl_Type = 
  Decl_Type {
    decl_TypeMods :: [Mod],
    decl_TypeName :: Type_Name,
    decl_TypeTparams :: [Type_Param],
    decl_TypeBounds :: Type_Bounds}
  deriving (Eq, Ord, Read, Show)

_Decl_Type = (Core.Name "hydra/langs/scala/meta.Decl.Type")

_Decl_Type_mods = (Core.FieldName "mods")

_Decl_Type_name = (Core.FieldName "name")

_Decl_Type_tparams = (Core.FieldName "tparams")

_Decl_Type_bounds = (Core.FieldName "bounds")

data Decl_Given = 
  Decl_Given {
    decl_GivenMods :: [Mod],
    decl_GivenName :: Data_Name,
    decl_GivenTparams :: [Type_Param],
    decl_GivenSparams :: [[Data_Param]],
    decl_GivenDecltpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Decl_Given = (Core.Name "hydra/langs/scala/meta.Decl.Given")

_Decl_Given_mods = (Core.FieldName "mods")

_Decl_Given_name = (Core.FieldName "name")

_Decl_Given_tparams = (Core.FieldName "tparams")

_Decl_Given_sparams = (Core.FieldName "sparams")

_Decl_Given_decltpe = (Core.FieldName "decltpe")

data Defn = 
  DefnVal Defn_Val |
  DefnVar Defn_Var |
  DefnGiven Defn_Given |
  DefnEnum Defn_Enum |
  DefnEnumCase Defn_EnumCase |
  DefnRepeatedEnumCase Defn_RepeatedEnumCase |
  DefnGivenAlias Defn_GivenAlias |
  DefnExtensionGroup Defn_ExtensionGroup |
  DefnDef Defn_Def |
  DefnMacro Defn_Macro |
  DefnType Defn_Type |
  DefnClass Defn_Class |
  DefnTrait Defn_Trait |
  DefnObject Defn_Object
  deriving (Eq, Ord, Read, Show)

_Defn = (Core.Name "hydra/langs/scala/meta.Defn")

_Defn_val = (Core.FieldName "val")

_Defn_var = (Core.FieldName "var")

_Defn_given = (Core.FieldName "given")

_Defn_enum = (Core.FieldName "enum")

_Defn_enumCase = (Core.FieldName "enumCase")

_Defn_repeatedEnumCase = (Core.FieldName "repeatedEnumCase")

_Defn_givenAlias = (Core.FieldName "givenAlias")

_Defn_extensionGroup = (Core.FieldName "extensionGroup")

_Defn_def = (Core.FieldName "def")

_Defn_macro = (Core.FieldName "macro")

_Defn_type = (Core.FieldName "type")

_Defn_class = (Core.FieldName "class")

_Defn_trait = (Core.FieldName "trait")

_Defn_object = (Core.FieldName "object")

data Defn_Val = 
  Defn_Val {
    defn_ValMods :: [Mod],
    defn_ValPats :: [Pat],
    defn_ValDecltpe :: (Maybe Type),
    defn_ValRhs :: Data}
  deriving (Eq, Ord, Read, Show)

_Defn_Val = (Core.Name "hydra/langs/scala/meta.Defn.Val")

_Defn_Val_mods = (Core.FieldName "mods")

_Defn_Val_pats = (Core.FieldName "pats")

_Defn_Val_decltpe = (Core.FieldName "decltpe")

_Defn_Val_rhs = (Core.FieldName "rhs")

data Defn_Var = 
  Defn_Var {
    defn_VarMods :: [Mod],
    defn_VarPats :: [Pat],
    defn_VarDecltpe :: Type,
    defn_VarRhs :: (Maybe Data)}
  deriving (Eq, Ord, Read, Show)

_Defn_Var = (Core.Name "hydra/langs/scala/meta.Defn.Var")

_Defn_Var_mods = (Core.FieldName "mods")

_Defn_Var_pats = (Core.FieldName "pats")

_Defn_Var_decltpe = (Core.FieldName "decltpe")

_Defn_Var_rhs = (Core.FieldName "rhs")

data Defn_Given = 
  Defn_Given {
    defn_GivenMods :: [Mod],
    defn_GivenName :: Name,
    defn_GivenTparams :: [[Type_Param]],
    defn_GivenSparams :: [[Data_Param]],
    defn_GivenTempl :: Template}
  deriving (Eq, Ord, Read, Show)

_Defn_Given = (Core.Name "hydra/langs/scala/meta.Defn.Given")

_Defn_Given_mods = (Core.FieldName "mods")

_Defn_Given_name = (Core.FieldName "name")

_Defn_Given_tparams = (Core.FieldName "tparams")

_Defn_Given_sparams = (Core.FieldName "sparams")

_Defn_Given_templ = (Core.FieldName "templ")

data Defn_Enum = 
  Defn_Enum {
    defn_EnumMods :: [Mod],
    defn_EnumName :: Type_Name,
    defn_EnumTparams :: [Type_Param],
    defn_EnumCtor :: Ctor_Primary,
    defn_EnumTemplate :: Template}
  deriving (Eq, Ord, Read, Show)

_Defn_Enum = (Core.Name "hydra/langs/scala/meta.Defn.Enum")

_Defn_Enum_mods = (Core.FieldName "mods")

_Defn_Enum_name = (Core.FieldName "name")

_Defn_Enum_tparams = (Core.FieldName "tparams")

_Defn_Enum_ctor = (Core.FieldName "ctor")

_Defn_Enum_template = (Core.FieldName "template")

data Defn_EnumCase = 
  Defn_EnumCase {
    defn_EnumCaseMods :: [Mod],
    defn_EnumCaseName :: Data_Name,
    defn_EnumCaseTparams :: [Type_Param],
    defn_EnumCaseCtor :: Ctor_Primary,
    defn_EnumCaseInits :: [Init]}
  deriving (Eq, Ord, Read, Show)

_Defn_EnumCase = (Core.Name "hydra/langs/scala/meta.Defn.EnumCase")

_Defn_EnumCase_mods = (Core.FieldName "mods")

_Defn_EnumCase_name = (Core.FieldName "name")

_Defn_EnumCase_tparams = (Core.FieldName "tparams")

_Defn_EnumCase_ctor = (Core.FieldName "ctor")

_Defn_EnumCase_inits = (Core.FieldName "inits")

data Defn_RepeatedEnumCase = 
  Defn_RepeatedEnumCase {
    defn_RepeatedEnumCaseMods :: [Mod],
    defn_RepeatedEnumCaseCases :: [Data_Name]}
  deriving (Eq, Ord, Read, Show)

_Defn_RepeatedEnumCase = (Core.Name "hydra/langs/scala/meta.Defn.RepeatedEnumCase")

_Defn_RepeatedEnumCase_mods = (Core.FieldName "mods")

_Defn_RepeatedEnumCase_cases = (Core.FieldName "cases")

data Defn_GivenAlias = 
  Defn_GivenAlias {
    defn_GivenAliasMods :: [Mod],
    defn_GivenAliasName :: Name,
    defn_GivenAliasTparams :: [[Type_Param]],
    defn_GivenAliasSparams :: [[Data_Param]],
    defn_GivenAliasDecltpe :: Type,
    defn_GivenAliasBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Defn_GivenAlias = (Core.Name "hydra/langs/scala/meta.Defn.GivenAlias")

_Defn_GivenAlias_mods = (Core.FieldName "mods")

_Defn_GivenAlias_name = (Core.FieldName "name")

_Defn_GivenAlias_tparams = (Core.FieldName "tparams")

_Defn_GivenAlias_sparams = (Core.FieldName "sparams")

_Defn_GivenAlias_decltpe = (Core.FieldName "decltpe")

_Defn_GivenAlias_body = (Core.FieldName "body")

data Defn_ExtensionGroup = 
  Defn_ExtensionGroup {
    defn_ExtensionGroupTparams :: [Type_Param],
    defn_ExtensionGroupParmss :: [[Data_Param]],
    defn_ExtensionGroupBody :: Stat}
  deriving (Eq, Ord, Read, Show)

_Defn_ExtensionGroup = (Core.Name "hydra/langs/scala/meta.Defn.ExtensionGroup")

_Defn_ExtensionGroup_tparams = (Core.FieldName "tparams")

_Defn_ExtensionGroup_parmss = (Core.FieldName "parmss")

_Defn_ExtensionGroup_body = (Core.FieldName "body")

data Defn_Def = 
  Defn_Def {
    defn_DefMods :: [Mod],
    defn_DefName :: Data_Name,
    defn_DefTparams :: [Type_Param],
    defn_DefParamss :: [[Data_Param]],
    defn_DefDecltpe :: (Maybe Type),
    defn_DefBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Defn_Def = (Core.Name "hydra/langs/scala/meta.Defn.Def")

_Defn_Def_mods = (Core.FieldName "mods")

_Defn_Def_name = (Core.FieldName "name")

_Defn_Def_tparams = (Core.FieldName "tparams")

_Defn_Def_paramss = (Core.FieldName "paramss")

_Defn_Def_decltpe = (Core.FieldName "decltpe")

_Defn_Def_body = (Core.FieldName "body")

data Defn_Macro = 
  Defn_Macro {
    defn_MacroMods :: [Mod],
    defn_MacroName :: Data_Name,
    defn_MacroTparams :: [Type_Param],
    defn_MacroParamss :: [[Data_Param]],
    defn_MacroDecltpe :: (Maybe Type),
    defn_MacroBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Defn_Macro = (Core.Name "hydra/langs/scala/meta.Defn.Macro")

_Defn_Macro_mods = (Core.FieldName "mods")

_Defn_Macro_name = (Core.FieldName "name")

_Defn_Macro_tparams = (Core.FieldName "tparams")

_Defn_Macro_paramss = (Core.FieldName "paramss")

_Defn_Macro_decltpe = (Core.FieldName "decltpe")

_Defn_Macro_body = (Core.FieldName "body")

data Defn_Type = 
  Defn_Type {
    defn_TypeMods :: [Mod],
    defn_TypeName :: Type_Name,
    defn_TypeTparams :: [Type_Param],
    defn_TypeBody :: Type}
  deriving (Eq, Ord, Read, Show)

_Defn_Type = (Core.Name "hydra/langs/scala/meta.Defn.Type")

_Defn_Type_mods = (Core.FieldName "mods")

_Defn_Type_name = (Core.FieldName "name")

_Defn_Type_tparams = (Core.FieldName "tparams")

_Defn_Type_body = (Core.FieldName "body")

data Defn_Class = 
  Defn_Class {
    defn_ClassMods :: [Mod],
    defn_ClassName :: Type_Name,
    defn_ClassTparams :: [Type_Param],
    defn_ClassCtor :: Ctor_Primary,
    defn_ClassTemplate :: Template}
  deriving (Eq, Ord, Read, Show)

_Defn_Class = (Core.Name "hydra/langs/scala/meta.Defn.Class")

_Defn_Class_mods = (Core.FieldName "mods")

_Defn_Class_name = (Core.FieldName "name")

_Defn_Class_tparams = (Core.FieldName "tparams")

_Defn_Class_ctor = (Core.FieldName "ctor")

_Defn_Class_template = (Core.FieldName "template")

data Defn_Trait = 
  Defn_Trait {
    defn_TraitMods :: [Mod],
    defn_TraitName :: Type_Name,
    defn_TraitTparams :: [Type_Param],
    defn_TraitCtor :: Ctor_Primary,
    defn_TraitTemplate :: Template}
  deriving (Eq, Ord, Read, Show)

_Defn_Trait = (Core.Name "hydra/langs/scala/meta.Defn.Trait")

_Defn_Trait_mods = (Core.FieldName "mods")

_Defn_Trait_name = (Core.FieldName "name")

_Defn_Trait_tparams = (Core.FieldName "tparams")

_Defn_Trait_ctor = (Core.FieldName "ctor")

_Defn_Trait_template = (Core.FieldName "template")

data Defn_Object = 
  Defn_Object {
    defn_ObjectName :: Data_Name}
  deriving (Eq, Ord, Read, Show)

_Defn_Object = (Core.Name "hydra/langs/scala/meta.Defn.Object")

_Defn_Object_name = (Core.FieldName "name")

data Pkg = 
  Pkg {
    pkgName :: Data_Name,
    pkgRef :: Data_Ref,
    pkgStats :: [Stat]}
  deriving (Eq, Ord, Read, Show)

_Pkg = (Core.Name "hydra/langs/scala/meta.Pkg")

_Pkg_name = (Core.FieldName "name")

_Pkg_ref = (Core.FieldName "ref")

_Pkg_stats = (Core.FieldName "stats")

data Pkg_Object = 
  Pkg_Object {
    pkg_ObjectMods :: [Mod],
    pkg_ObjectName :: Data_Name,
    pkg_ObjectTemplate :: Template}
  deriving (Eq, Ord, Read, Show)

_Pkg_Object = (Core.Name "hydra/langs/scala/meta.Pkg.Object")

_Pkg_Object_mods = (Core.FieldName "mods")

_Pkg_Object_name = (Core.FieldName "name")

_Pkg_Object_template = (Core.FieldName "template")

data Ctor = 
  CtorPrimary Ctor_Primary |
  CtorSecondary Ctor_Secondary
  deriving (Eq, Ord, Read, Show)

_Ctor = (Core.Name "hydra/langs/scala/meta.Ctor")

_Ctor_primary = (Core.FieldName "primary")

_Ctor_secondary = (Core.FieldName "secondary")

data Ctor_Primary = 
  Ctor_Primary {
    ctor_PrimaryMods :: [Mod],
    ctor_PrimaryName :: Name,
    ctor_PrimaryParamss :: [[Data_Param]]}
  deriving (Eq, Ord, Read, Show)

_Ctor_Primary = (Core.Name "hydra/langs/scala/meta.Ctor.Primary")

_Ctor_Primary_mods = (Core.FieldName "mods")

_Ctor_Primary_name = (Core.FieldName "name")

_Ctor_Primary_paramss = (Core.FieldName "paramss")

data Ctor_Secondary = 
  Ctor_Secondary {
    ctor_SecondaryMods :: [Mod],
    ctor_SecondaryName :: Name,
    ctor_SecondaryParamss :: [[Data_Param]],
    ctor_SecondaryInit :: Init,
    ctor_SecondaryStats :: [Stat]}
  deriving (Eq, Ord, Read, Show)

_Ctor_Secondary = (Core.Name "hydra/langs/scala/meta.Ctor.Secondary")

_Ctor_Secondary_mods = (Core.FieldName "mods")

_Ctor_Secondary_name = (Core.FieldName "name")

_Ctor_Secondary_paramss = (Core.FieldName "paramss")

_Ctor_Secondary_init = (Core.FieldName "init")

_Ctor_Secondary_stats = (Core.FieldName "stats")

data Init = 
  Init {
    initTpe :: Type,
    initName :: Name,
    initArgss :: [[Data]]}
  deriving (Eq, Ord, Read, Show)

_Init = (Core.Name "hydra/langs/scala/meta.Init")

_Init_tpe = (Core.FieldName "tpe")

_Init_name = (Core.FieldName "name")

_Init_argss = (Core.FieldName "argss")

data Self = 
  Self {}
  deriving (Eq, Ord, Read, Show)

_Self = (Core.Name "hydra/langs/scala/meta.Self")

data Template = 
  Template {
    templateEarly :: [Stat],
    templateInits :: [Init],
    templateSelf :: Self,
    templateStats :: [Stat]}
  deriving (Eq, Ord, Read, Show)

_Template = (Core.Name "hydra/langs/scala/meta.Template")

_Template_early = (Core.FieldName "early")

_Template_inits = (Core.FieldName "inits")

_Template_self = (Core.FieldName "self")

_Template_stats = (Core.FieldName "stats")

data Mod = 
  ModAnnot Mod_Annot |
  ModPrivate Mod_Private |
  ModProtected Mod_Protected |
  ModImplicit  |
  ModFinal  |
  ModSealed  |
  ModOpen  |
  ModSuper  |
  ModOverride  |
  ModCase  |
  ModAbstract  |
  ModCovariant  |
  ModContravariant  |
  ModLazy  |
  ModValParam  |
  ModVarParam  |
  ModInfix  |
  ModInline  |
  ModUsing  |
  ModOpaque  |
  ModTransparent 
  deriving (Eq, Ord, Read, Show)

_Mod = (Core.Name "hydra/langs/scala/meta.Mod")

_Mod_annot = (Core.FieldName "annot")

_Mod_private = (Core.FieldName "private")

_Mod_protected = (Core.FieldName "protected")

_Mod_implicit = (Core.FieldName "implicit")

_Mod_final = (Core.FieldName "final")

_Mod_sealed = (Core.FieldName "sealed")

_Mod_open = (Core.FieldName "open")

_Mod_super = (Core.FieldName "super")

_Mod_override = (Core.FieldName "override")

_Mod_case = (Core.FieldName "case")

_Mod_abstract = (Core.FieldName "abstract")

_Mod_covariant = (Core.FieldName "covariant")

_Mod_contravariant = (Core.FieldName "contravariant")

_Mod_lazy = (Core.FieldName "lazy")

_Mod_valParam = (Core.FieldName "valParam")

_Mod_varParam = (Core.FieldName "varParam")

_Mod_infix = (Core.FieldName "infix")

_Mod_inline = (Core.FieldName "inline")

_Mod_using = (Core.FieldName "using")

_Mod_opaque = (Core.FieldName "opaque")

_Mod_transparent = (Core.FieldName "transparent")

data Mod_Annot = 
  Mod_Annot {
    mod_AnnotInit :: Init}
  deriving (Eq, Ord, Read, Show)

_Mod_Annot = (Core.Name "hydra/langs/scala/meta.Mod.Annot")

_Mod_Annot_init = (Core.FieldName "init")

data Mod_Private = 
  Mod_Private {
    mod_PrivateWithin :: Ref}
  deriving (Eq, Ord, Read, Show)

_Mod_Private = (Core.Name "hydra/langs/scala/meta.Mod.Private")

_Mod_Private_within = (Core.FieldName "within")

data Mod_Protected = 
  Mod_Protected {
    mod_ProtectedWithin :: Ref}
  deriving (Eq, Ord, Read, Show)

_Mod_Protected = (Core.Name "hydra/langs/scala/meta.Mod.Protected")

_Mod_Protected_within = (Core.FieldName "within")

data Enumerator = 
  EnumeratorGenerator Enumerator_Generator |
  EnumeratorCaseGenerator Enumerator_CaseGenerator |
  EnumeratorVal Enumerator_Val |
  EnumeratorGuard Enumerator_Guard
  deriving (Eq, Ord, Read, Show)

_Enumerator = (Core.Name "hydra/langs/scala/meta.Enumerator")

_Enumerator_generator = (Core.FieldName "generator")

_Enumerator_caseGenerator = (Core.FieldName "caseGenerator")

_Enumerator_val = (Core.FieldName "val")

_Enumerator_guard = (Core.FieldName "guard")

data Enumerator_Generator = 
  Enumerator_Generator {
    enumerator_GeneratorPat :: Pat,
    enumerator_GeneratorRhs :: Data}
  deriving (Eq, Ord, Read, Show)

_Enumerator_Generator = (Core.Name "hydra/langs/scala/meta.Enumerator.Generator")

_Enumerator_Generator_pat = (Core.FieldName "pat")

_Enumerator_Generator_rhs = (Core.FieldName "rhs")

data Enumerator_CaseGenerator = 
  Enumerator_CaseGenerator {
    enumerator_CaseGeneratorPat :: Pat,
    enumerator_CaseGeneratorRhs :: Data}
  deriving (Eq, Ord, Read, Show)

_Enumerator_CaseGenerator = (Core.Name "hydra/langs/scala/meta.Enumerator.CaseGenerator")

_Enumerator_CaseGenerator_pat = (Core.FieldName "pat")

_Enumerator_CaseGenerator_rhs = (Core.FieldName "rhs")

data Enumerator_Val = 
  Enumerator_Val {
    enumerator_ValPat :: Pat,
    enumerator_ValRhs :: Data}
  deriving (Eq, Ord, Read, Show)

_Enumerator_Val = (Core.Name "hydra/langs/scala/meta.Enumerator.Val")

_Enumerator_Val_pat = (Core.FieldName "pat")

_Enumerator_Val_rhs = (Core.FieldName "rhs")

data Enumerator_Guard = 
  Enumerator_Guard {
    enumerator_GuardCond :: Data}
  deriving (Eq, Ord, Read, Show)

_Enumerator_Guard = (Core.Name "hydra/langs/scala/meta.Enumerator.Guard")

_Enumerator_Guard_cond = (Core.FieldName "cond")

data ImportExportStat = 
  ImportExportStatImport Import |
  ImportExportStatExport Export
  deriving (Eq, Ord, Read, Show)

_ImportExportStat = (Core.Name "hydra/langs/scala/meta.ImportExportStat")

_ImportExportStat_import = (Core.FieldName "import")

_ImportExportStat_export = (Core.FieldName "export")

data Import = 
  Import {
    importImporters :: [Importer]}
  deriving (Eq, Ord, Read, Show)

_Import = (Core.Name "hydra/langs/scala/meta.Import")

_Import_importers = (Core.FieldName "importers")

data Export = 
  Export {
    exportImporters :: [Importer]}
  deriving (Eq, Ord, Read, Show)

_Export = (Core.Name "hydra/langs/scala/meta.Export")

_Export_importers = (Core.FieldName "importers")

data Importer = 
  Importer {
    importerRef :: Data_Ref,
    importerImportees :: [Importee]}
  deriving (Eq, Ord, Read, Show)

_Importer = (Core.Name "hydra/langs/scala/meta.Importer")

_Importer_ref = (Core.FieldName "ref")

_Importer_importees = (Core.FieldName "importees")

data Importee = 
  ImporteeWildcard  |
  ImporteeGiven Importee_Given |
  ImporteeGivenAll  |
  ImporteeName Importee_Name |
  ImporteeRename Importee_Rename |
  ImporteeUnimport Importee_Unimport
  deriving (Eq, Ord, Read, Show)

_Importee = (Core.Name "hydra/langs/scala/meta.Importee")

_Importee_wildcard = (Core.FieldName "wildcard")

_Importee_given = (Core.FieldName "given")

_Importee_givenAll = (Core.FieldName "givenAll")

_Importee_name = (Core.FieldName "name")

_Importee_rename = (Core.FieldName "rename")

_Importee_unimport = (Core.FieldName "unimport")

data Importee_Given = 
  Importee_Given {
    importee_GivenTpe :: Type}
  deriving (Eq, Ord, Read, Show)

_Importee_Given = (Core.Name "hydra/langs/scala/meta.Importee.Given")

_Importee_Given_tpe = (Core.FieldName "tpe")

data Importee_Name = 
  Importee_Name {
    importee_NameName :: Name}
  deriving (Eq, Ord, Read, Show)

_Importee_Name = (Core.Name "hydra/langs/scala/meta.Importee.Name")

_Importee_Name_name = (Core.FieldName "name")

data Importee_Rename = 
  Importee_Rename {
    importee_RenameName :: Name,
    importee_RenameRename :: Name}
  deriving (Eq, Ord, Read, Show)

_Importee_Rename = (Core.Name "hydra/langs/scala/meta.Importee.Rename")

_Importee_Rename_name = (Core.FieldName "name")

_Importee_Rename_rename = (Core.FieldName "rename")

data Importee_Unimport = 
  Importee_Unimport {
    importee_UnimportName :: Name}
  deriving (Eq, Ord, Read, Show)

_Importee_Unimport = (Core.Name "hydra/langs/scala/meta.Importee.Unimport")

_Importee_Unimport_name = (Core.FieldName "name")

data CaseTree = 
  CaseTreeCase Case |
  CaseTreeTypeCase TypeCase
  deriving (Eq, Ord, Read, Show)

_CaseTree = (Core.Name "hydra/langs/scala/meta.CaseTree")

_CaseTree_case = (Core.FieldName "case")

_CaseTree_typeCase = (Core.FieldName "typeCase")

data Case = 
  Case {
    casePat :: Pat,
    caseCond :: (Maybe Data),
    caseBody :: Data}
  deriving (Eq, Ord, Read, Show)

_Case = (Core.Name "hydra/langs/scala/meta.Case")

_Case_pat = (Core.FieldName "pat")

_Case_cond = (Core.FieldName "cond")

_Case_body = (Core.FieldName "body")

data TypeCase = 
  TypeCase {
    typeCasePat :: Type,
    typeCaseBody :: Type}
  deriving (Eq, Ord, Read, Show)

_TypeCase = (Core.Name "hydra/langs/scala/meta.TypeCase")

_TypeCase_pat = (Core.FieldName "pat")

_TypeCase_body = (Core.FieldName "body")

data Source = 
  Source {
    sourceStats :: [Stat]}
  deriving (Eq, Ord, Read, Show)

_Source = (Core.Name "hydra/langs/scala/meta.Source")

_Source_stats = (Core.FieldName "stats")

data Quasi = 
  Quasi {}
  deriving (Eq, Ord, Read, Show)

_Quasi = (Core.Name "hydra/langs/scala/meta.Quasi")