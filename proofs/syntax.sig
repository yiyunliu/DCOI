tm : Type
nat : Type
T : Type

tAbs : T -> (tm -> tm) -> tm
tApp : tm -> T -> tm -> tm
tPi : T -> tm -> (tm -> tm) -> tm
tUniv : nat -> tm
tVoid : tm
tAbsurd : tm -> tm
tEq : T -> tm -> tm -> tm
tJ : T -> tm -> tm -> tm
tRefl : tm
tSig : T -> tm -> (tm -> tm) -> tm
tPack : T -> tm -> tm -> tm
tLet : T -> T -> tm -> (tm -> tm -> tm) -> tm
tZero : tm
tSuc : tm -> tm
tInd : T -> tm -> (tm -> tm -> tm) -> tm -> tm
tNat : tm
tTT : tm
tSeq : T -> tm -> tm -> tm
tUnit : tm