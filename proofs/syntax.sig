tm(var_tm) : Type
nat : Type
T : Type

tAbs : T -> (bind tm in tm) -> tm
tApp : tm -> T -> tm -> tm
tPi : T -> tm -> (bind tm in tm) -> tm
tUniv : nat -> tm
tVoid : tm
tAbsurd : tm -> tm
tEq : T -> tm -> tm -> tm
tJ : T -> tm -> tm -> tm
tRefl : tm
tSig : T -> tm -> (bind tm in tm) -> tm
tPack : T -> tm -> tm -> tm
tLet : T -> T -> tm -> (bind tm,tm in tm) -> tm
tZero : tm
tSuc : tm -> tm
tInd : T -> tm -> (bind tm,tm in tm) -> tm -> tm
tNat : tm
tTT : tm
tSeq : T -> tm -> tm -> tm
tUnit : tm
