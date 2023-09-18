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
annotatedTermT = Types.apply (TypeVariable _Annotated) termT :: Type
annotatedTypeT = Types.apply (TypeVariable _Annotated) typeT :: Type
applicationT = TypeVariable _Application :: Type
applicationTypeT = TypeVariable _ApplicationType :: Type
booleanT = Types.boolean
caseStatementT = TypeVariable _CaseStatement :: Type
elementT = TypeVariable _Element :: Type
eliminationT = TypeVariable _Elimination :: Type
fieldT = TypeVariable _Field :: Type
fieldTypeT = TypeVariable _FieldType :: Type
flowGraphATypeA = Types.apply (Types.apply (TypeVariable _Flow) graphT) typeT :: Type
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
lambdaT = TypeVariable _Lambda :: Type
lambdaTypeT = Types.apply (TypeVariable _LambdaType) aT :: Type
languageT = Types.apply (TypeVariable _Language) aT :: Type
letT = TypeVariable _Let :: Type
listT = Types.list
mapTypeA = Types.apply (TypeVariable _MapType) (Types.var "a") :: Type
nameT = TypeVariable _Name
nominalTermT = Types.apply (TypeVariable _Nominal) termT :: Type
nominalTypeT = Types.apply (TypeVariable _Nominal) typeT :: Type
optionalCasesT = TypeVariable _OptionalCases :: Type
pairT = Types.pair
recordT = TypeVariable _Record :: Type
rowTypeT = TypeVariable _RowType :: Type
sT = Types.var "s" :: Type
setT = TypeSet
stringT = Types.string :: Type
sumT = TypeVariable _Sum :: Type
termT = TypeVariable _Term :: Type
traceT = TypeVariable _Trace
typeT = TypeVariable _Type :: Type
unitT = Types.unit :: Type
xT = Types.var "x" :: Type
