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

aT = Types.var "a" :: Type Kv
annotatedTermA = Types.apply (Types.apply (TypeVariable _Annotated) termA) (Types.var "a") :: Type Kv
annotatedTypeA = Types.apply (Types.apply (TypeVariable _Annotated) typeA) (Types.var "a") :: Type Kv
applicationA = Types.apply (TypeVariable _Application) (Types.var "a") :: Type Kv
applicationTypeA = Types.apply (TypeVariable _ApplicationType) (Types.var "a") :: Type Kv
booleanT = Types.boolean
caseStatementA = Types.apply (TypeVariable _CaseStatement) (Types.var "a") :: Type Kv
elementA = Types.apply (TypeVariable _Element) aT :: Type Kv
eliminationA = Types.apply (TypeVariable _Elimination) (Types.var "a") :: Type Kv
fieldA = Types.apply (TypeVariable _Field) aT :: Type Kv
fieldTypeA = Types.apply (TypeVariable _FieldType) aT :: Type Kv
flowGraphATypeA = Types.apply (Types.apply (TypeVariable _Flow) graphA) typeA :: Type Kv
flowS1A = flowT (Types.var "s1") (Types.var "a") :: Type Kv
flowS2A = flowT (Types.var "s2") (Types.var "a") :: Type Kv
flowSA = flowT (Types.var "s") (Types.var "a") :: Type Kv
flowSS = flowT (Types.var "s") (Types.var "s") :: Type Kv
flowSY = flowT (Types.var "s") (Types.var "y") :: Type Kv
flowStateSS = flowStateT (Types.var "s") (Types.var "s") :: Type Kv
flowStateT s x = Types.apply (Types.apply (TypeVariable _FlowState) s) x
flowT s x = Types.apply (Types.apply (TypeVariable _Flow) s) x
functionA = Types.apply (TypeVariable _Function) (Types.var "a") :: Type Kv
functionT = Types.function
functionTypeA = Types.apply (TypeVariable _FunctionType) (Types.var "a") :: Type Kv
graphA = Types.apply (TypeVariable _Graph) aT :: Type Kv
injectionA = Types.apply (TypeVariable _Injection) (Types.var "a") :: Type Kv
lambdaA = Types.apply (TypeVariable _Lambda) (Types.var "a") :: Type Kv
lambdaTypeA = Types.apply (TypeVariable _LambdaType) aT :: Type Kv
languageA = Types.apply (TypeVariable _Language) aT :: Type Kv
letA = Types.apply (TypeVariable _Let) (Types.var "a") :: Type Kv
listT = Types.list
mapTypeA = Types.apply (TypeVariable _MapType) (Types.var "a") :: Type Kv
nameT = TypeVariable _Name
nominalTermA = Types.apply (TypeVariable _Nominal) termA :: Type Kv
nominalTypeA = Types.apply (TypeVariable _Nominal) typeA :: Type Kv
optionalCasesA = Types.apply (TypeVariable _OptionalCases) (Types.var "a") :: Type Kv
pairT = Types.pair
recordA = Types.apply (TypeVariable _Record) (Types.var "a") :: Type Kv
rowTypeA = Types.apply (TypeVariable _RowType) (Types.var "a") :: Type Kv
sT = Types.var "s" :: Type Kv
setT = TypeSet
stringT = Types.string :: Type Kv
sumA = Types.apply (TypeVariable _Sum) (Types.var "a") :: Type Kv
termA = Types.apply (TypeVariable _Term) aT :: Type Kv
termKV = Types.apply (TypeVariable _Term) (TypeVariable _Kv) :: Type Kv
traceT = TypeVariable _Trace
typeA = Types.apply (TypeVariable _Type) aT :: Type Kv
unitT = Types.unit :: Type Kv
xT = Types.var "x" :: Type Kv
