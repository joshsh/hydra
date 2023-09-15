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
annotatedTermA = Types.apply (Types.apply (TypeVariable _Annotated) termA) (Types.var "a") :: Type
annotatedTypeA = Types.apply (Types.apply (TypeVariable _Annotated) typeA) (Types.var "a") :: Type
applicationA = Types.apply (TypeVariable _Application) (Types.var "a") :: Type
applicationTypeA = Types.apply (TypeVariable _ApplicationType) (Types.var "a") :: Type
booleanT = Types.boolean
caseStatementA = Types.apply (TypeVariable _CaseStatement) (Types.var "a") :: Type
elementA = Types.apply (TypeVariable _Element) aT :: Type
eliminationA = Types.apply (TypeVariable _Elimination) (Types.var "a") :: Type
fieldA = Types.apply (TypeVariable _Field) aT :: Type
fieldTypeA = Types.apply (TypeVariable _FieldType) aT :: Type
flowGraphATypeA = Types.apply (Types.apply (TypeVariable _Flow) graphA) typeA :: Type
flowS1A = flowT (Types.var "s1") (Types.var "a") :: Type
flowS2A = flowT (Types.var "s2") (Types.var "a") :: Type
flowSA = flowT (Types.var "s") (Types.var "a") :: Type
flowSS = flowT (Types.var "s") (Types.var "s") :: Type
flowSY = flowT (Types.var "s") (Types.var "y") :: Type
flowStateSS = flowStateT (Types.var "s") (Types.var "s") :: Type
flowStateT s x = Types.apply (Types.apply (TypeVariable _FlowState) s) x
flowT s x = Types.apply (Types.apply (TypeVariable _Flow) s) x
functionA = Types.apply (TypeVariable _Function) (Types.var "a") :: Type
functionT = Types.function
functionTypeA = Types.apply (TypeVariable _FunctionType) (Types.var "a") :: Type
graphA = Types.apply (TypeVariable _Graph) aT :: Type
injectionA = Types.apply (TypeVariable _Injection) (Types.var "a") :: Type
lambdaA = Types.apply (TypeVariable _Lambda) (Types.var "a") :: Type
lambdaTypeA = Types.apply (TypeVariable _LambdaType) aT :: Type
languageA = Types.apply (TypeVariable _Language) aT :: Type
letA = Types.apply (TypeVariable _Let) (Types.var "a") :: Type
listT = Types.list
mapTypeA = Types.apply (TypeVariable _MapType) (Types.var "a") :: Type
nameT = TypeVariable _Name
nominalTermA = Types.apply (TypeVariable _Nominal) termA :: Type
nominalTypeA = Types.apply (TypeVariable _Nominal) typeA :: Type
optionalCasesA = Types.apply (TypeVariable _OptionalCases) (Types.var "a") :: Type
pairT = Types.pair
recordA = Types.apply (TypeVariable _Record) (Types.var "a") :: Type
rowTypeA = Types.apply (TypeVariable _RowType) (Types.var "a") :: Type
sT = Types.var "s" :: Type
setT = TypeSet
stringT = Types.string :: Type
sumA = Types.apply (TypeVariable _Sum) (Types.var "a") :: Type
termA = Types.apply (TypeVariable _Term) aT :: Type
termKV = Types.apply (TypeVariable _Term) (TypeVariable _Kv) :: Type
traceT = TypeVariable _Trace
typeA = Types.apply (TypeVariable _Type) aT :: Type
unitT = Types.unit :: Type
xT = Types.var "x" :: Type
