module Hydra.Dsl.ShorthandTypes where

import Hydra.Coders
import Hydra.Core
import Hydra.Compute
import Hydra.Graph
import qualified Hydra.Dsl.Types as Types

import qualified Data.Map as M
import qualified Data.Set as S


eqA = (M.fromList [(Name "a", S.fromList [TypeClassEquality])])
ordA = (M.fromList [(Name "a", S.fromList [TypeClassOrdering])])

aT = Types.var "a" :: Type
annotatedT t = Types.apply (TypeVariable _Annotated) t :: Type
annotatedTermT = annotatedT termT :: Type
annotatedTypeT = annotatedT typeT :: Type
applicationT = TypeVariable _Application :: Type
applicationTypeT = TypeVariable _ApplicationType :: Type
bigfloatT = Types.bigfloat
booleanT = Types.boolean
caseStatementT = TypeVariable _CaseStatement :: Type
elementT = TypeVariable _Element :: Type
eliminationT = TypeVariable _Elimination :: Type
fieldT = TypeVariable _Field :: Type
fieldTypeT = TypeVariable _FieldType :: Type
floatValueT = TypeVariable _FloatValue :: Type
float32T = Types.float32 :: Type
float64T = Types.float64 :: Type
flowGraphATypeA = flowT graphT typeT :: Type
flowS1A = flowT (Types.var "s1") (Types.var "a") :: Type
flowS2A = flowT (Types.var "s2") (Types.var "a") :: Type
flowSA = flowT (Types.var "s") (Types.var "a") :: Type
flowSS = flowT (Types.var "s") (Types.var "s") :: Type
flowSY = flowT (Types.var "s") (Types.var "y") :: Type
flowStateSS = flowStateT (Types.var "s") (Types.var "s") :: Type
flowStateT s x = Types.apply (Types.apply (TypeVariable _FlowState) s) x
flowT s x = Types.apply (Types.apply (TypeVariable _Flow) s) x
functionT = TypeVariable _Function :: Type
funT = Types.function
functionTypeT = TypeVariable _FunctionType :: Type
graphT = TypeVariable _Graph :: Type
injectionT = TypeVariable _Injection :: Type
integerValueT = TypeVariable _IntegerValue :: Type
lambdaT = TypeVariable _Lambda :: Type
lambdaTypeT = TypeVariable _LambdaType :: Type
languageT = TypeVariable _Language :: Type
letT = TypeVariable _Let :: Type
listT = Types.list
mapTypeT = TypeVariable _MapType :: Type
nameT = TypeVariable _Name
nominalTermT = Types.apply (TypeVariable _Nominal) termT :: Type
nominalTypeT = Types.apply (TypeVariable _Nominal) typeT :: Type
optionalCasesT = TypeVariable _OptionalCases :: Type
optionalT = Types.optional :: Type -> Type
pairT = Types.pair
recordT = TypeVariable _Record :: Type
rowTypeT = TypeVariable _RowType :: Type
sT = Types.var "s" :: Type
setT = TypeSet
stringT = Types.string :: Type
sumT = TypeVariable _Sum :: Type
termT = TypeVariable _Term :: Type
traceT = TypeVariable _Trace :: Type
typeT = TypeVariable _Type :: Type
unitT = Types.unit :: Type
xT = Types.var "x" :: Type
