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

aT = Types.var "a" :: Type a
annotatedTermA = Types.apply (Types.apply (TypeVariable _Annotated) termA) (Types.var "a") :: Type a
annotatedTypeA = Types.apply (Types.apply (TypeVariable _Annotated) typeA) (Types.var "a") :: Type a
applicationA = Types.apply (TypeVariable _Application) (Types.var "a") :: Type a
applicationTypeA = Types.apply (TypeVariable _ApplicationType) (Types.var "a") :: Type a
booleanT = Types.boolean
caseStatementA = Types.apply (TypeVariable _CaseStatement) (Types.var "a") :: Type a
elementA = Types.apply (TypeVariable _Element) aT :: Type a
eliminationA = Types.apply (TypeVariable _Elimination) (Types.var "a") :: Type a
fieldA = Types.apply (TypeVariable _Field) aT :: Type a
fieldTypeA = Types.apply (TypeVariable _FieldType) aT :: Type a
flowGraphATypeA = Types.apply (Types.apply (TypeVariable _Flow) graphA) typeA :: Type a
flowS1A = flowT (Types.var "s1") (Types.var "a") :: Type a
flowS2A = flowT (Types.var "s2") (Types.var "a") :: Type a
flowSA = flowT (Types.var "s") (Types.var "a") :: Type a
flowSS = flowT (Types.var "s") (Types.var "s") :: Type a
flowSY = flowT (Types.var "s") (Types.var "y") :: Type a
flowStateSS = flowStateT (Types.var "s") (Types.var "s") :: Type a
flowStateT s x = Types.apply (Types.apply (TypeVariable _FlowState) s) x
flowT s x = Types.apply (Types.apply (TypeVariable _Flow) s) x
functionA = Types.apply (TypeVariable _Function) (Types.var "a") :: Type a
functionT = Types.function
functionTypeA = Types.apply (TypeVariable _FunctionType) (Types.var "a") :: Type a
graphA = Types.apply (TypeVariable _Graph) aT :: Type a
injectionA = Types.apply (TypeVariable _Injection) (Types.var "a") :: Type a
lambdaA = Types.apply (TypeVariable _Lambda) (Types.var "a") :: Type a
lambdaTypeA = Types.apply (TypeVariable _LambdaType) aT :: Type a
languageA = Types.apply (TypeVariable _Language) aT :: Type a
letA = Types.apply (TypeVariable _Let) (Types.var "a") :: Type a
listT = Types.list
mapTypeA = Types.apply (TypeVariable _MapType) (Types.var "a") :: Type a
nameT = TypeVariable _Name
nominalTermA = Types.apply (TypeVariable _Nominal) termA :: Type a
nominalTypeA = Types.apply (TypeVariable _Nominal) typeA :: Type a
optionalCasesA = Types.apply (TypeVariable _OptionalCases) (Types.var "a") :: Type a
pairT = Types.pair
recordA = Types.apply (TypeVariable _Record) (Types.var "a") :: Type a
rowTypeA = Types.apply (TypeVariable _RowType) (Types.var "a") :: Type a
sT = Types.var "s" :: Type a
setT = TypeSet
stringT = Types.string :: Type a
sumA = Types.apply (TypeVariable _Sum) (Types.var "a") :: Type a
termA = Types.apply (TypeVariable _Term) aT :: Type a
termKV = Types.apply (TypeVariable _Term) (TypeVariable _Kv) :: Type a
traceT = TypeVariable _Trace
typeA = Types.apply (TypeVariable _Type) aT :: Type a
unitT = Types.unit :: Type a
xT = Types.var "x" :: Type a
