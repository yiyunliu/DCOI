Require Export Lattice.All.
Require Export core unscoped.
Require Import Setoid Morphisms Relation_Definitions.

(* Equations (transitively required by Lattice.All) marks both arguments
   of [eq_refl] implicit, which breaks the autosubst-ocaml-generated terms
   of the form [(eq_refl s0)]. Restore the legacy alternative arity. *)
#[global] Arguments eq_refl {A}%_type_scope {x}%_type_scope, [_] _.

Module Type syntax_sig
  (Export lattice : Lattice).



Module Core.

Inductive tm : Type :=
  | var_tm : nat -> tm
  | tAbs : T -> tm -> tm
  | tApp : tm -> T -> tm -> tm
  | tPi : T -> tm -> tm -> tm
  | tUniv : nat -> tm
  | tVoid : tm
  | tAbsurd : tm -> tm
  | tEq : T -> tm -> tm -> tm
  | tJ : T -> tm -> tm -> tm
  | tRefl : tm
  | tSig : T -> tm -> tm -> tm
  | tPack : T -> tm -> tm -> tm
  | tLet : T -> T -> tm -> tm -> tm
  | tZero : tm
  | tSuc : tm -> tm
  | tInd : T -> tm -> tm -> tm -> tm
  | tNat : tm
  | tTT : tm
  | tSeq : T -> tm -> tm -> tm
  | tUnit : tm.

Lemma congr_tAbs {s0 : T} {s1 : tm} {t0 : T} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : tAbs s0 s1 = tAbs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tAbs x s1) H0))
         (ap (fun x => tAbs t0 x) H1)).
Qed.

Lemma congr_tApp {s0 : tm} {s1 : T} {s2 : tm} {t0 : tm} {t1 : T} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tApp s0 s1 s2 = tApp t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tApp x s1 s2) H0))
            (ap (fun x => tApp t0 x s2) H1))
         (ap (fun x => tApp t0 t1 x) H2)).
Qed.

Lemma congr_tPi {s0 : T} {s1 : tm} {s2 : tm} {t0 : T} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) : tPi s0 s1 s2 = tPi t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tPi x s1 s2) H0))
            (ap (fun x => tPi t0 x s2) H1))
         (ap (fun x => tPi t0 t1 x) H2)).
Qed.

Lemma congr_tUniv {s0 : nat} {t0 : nat} (H0 : s0 = t0) : tUniv s0 = tUniv t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tUniv x) H0)).
Qed.

Lemma congr_tVoid : tVoid = tVoid.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tAbsurd {s0 : tm} {t0 : tm} (H0 : s0 = t0) :
  tAbsurd s0 = tAbsurd t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tAbsurd x) H0)).
Qed.

Lemma congr_tEq {s0 : T} {s1 : tm} {s2 : tm} {t0 : T} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) : tEq s0 s1 s2 = tEq t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tEq x s1 s2) H0))
            (ap (fun x => tEq t0 x s2) H1))
         (ap (fun x => tEq t0 t1 x) H2)).
Qed.

Lemma congr_tJ {s0 : T} {s1 : tm} {s2 : tm} {t0 : T} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) : tJ s0 s1 s2 = tJ t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tJ x s1 s2) H0))
            (ap (fun x => tJ t0 x s2) H1))
         (ap (fun x => tJ t0 t1 x) H2)).
Qed.

Lemma congr_tRefl : tRefl = tRefl.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tSig {s0 : T} {s1 : tm} {s2 : tm} {t0 : T} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tSig s0 s1 s2 = tSig t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tSig x s1 s2) H0))
            (ap (fun x => tSig t0 x s2) H1))
         (ap (fun x => tSig t0 t1 x) H2)).
Qed.

Lemma congr_tPack {s0 : T} {s1 : tm} {s2 : tm} {t0 : T} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tPack s0 s1 s2 = tPack t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tPack x s1 s2) H0))
            (ap (fun x => tPack t0 x s2) H1))
         (ap (fun x => tPack t0 t1 x) H2)).
Qed.

Lemma congr_tLet {s0 : T} {s1 : T} {s2 : tm} {s3 : tm} {t0 : T} {t1 : T}
  {t2 : tm} {t3 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) : tLet s0 s1 s2 s3 = tLet t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => tLet x s1 s2 s3) H0))
               (ap (fun x => tLet t0 x s2 s3) H1))
            (ap (fun x => tLet t0 t1 x s3) H2))
         (ap (fun x => tLet t0 t1 t2 x) H3)).
Qed.

Lemma congr_tZero : tZero = tZero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tSuc {s0 : tm} {t0 : tm} (H0 : s0 = t0) : tSuc s0 = tSuc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tSuc x) H0)).
Qed.

Lemma congr_tInd {s0 : T} {s1 : tm} {s2 : tm} {s3 : tm} {t0 : T} {t1 : tm}
  {t2 : tm} {t3 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) : tInd s0 s1 s2 s3 = tInd t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => tInd x s1 s2 s3) H0))
               (ap (fun x => tInd t0 x s2 s3) H1))
            (ap (fun x => tInd t0 t1 x s3) H2))
         (ap (fun x => tInd t0 t1 t2 x) H3)).
Qed.

Lemma congr_tNat : tNat = tNat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tTT : tTT = tTT.
Proof.
exact (eq_refl).
Qed.

Lemma congr_tSeq {s0 : T} {s1 : tm} {s2 : tm} {t0 : T} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  tSeq s0 s1 s2 = tSeq t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => tSeq x s1 s2) H0))
            (ap (fun x => tSeq t0 x s2) H1))
         (ap (fun x => tSeq t0 t1 x) H2)).
Qed.

Lemma congr_tUnit : tUnit = tUnit.
Proof.
exact (eq_refl).
Qed.

Lemma upRen_tm_tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_tm (xi_tm : nat -> nat) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => var_tm (xi_tm s0)
  | tAbs s0 s1 => tAbs s0 (ren_tm (upRen_tm_tm xi_tm) s1)
  | tApp s0 s1 s2 => tApp (ren_tm xi_tm s0) s1 (ren_tm xi_tm s2)
  | tPi s0 s1 s2 => tPi s0 (ren_tm xi_tm s1) (ren_tm (upRen_tm_tm xi_tm) s2)
  | tUniv s0 => tUniv s0
  | tVoid => tVoid
  | tAbsurd s0 => tAbsurd (ren_tm xi_tm s0)
  | tEq s0 s1 s2 => tEq s0 (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | tJ s0 s1 s2 => tJ s0 (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | tRefl => tRefl
  | tSig s0 s1 s2 =>
      tSig s0 (ren_tm xi_tm s1) (ren_tm (upRen_tm_tm xi_tm) s2)
  | tPack s0 s1 s2 => tPack s0 (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | tLet s0 s1 s2 s3 =>
      tLet s0 s1 (ren_tm xi_tm s2)
        (ren_tm (upRen_tm_tm (upRen_tm_tm xi_tm)) s3)
  | tZero => tZero
  | tSuc s0 => tSuc (ren_tm xi_tm s0)
  | tInd s0 s1 s2 s3 =>
      tInd s0 (ren_tm xi_tm s1) (ren_tm (upRen_tm_tm (upRen_tm_tm xi_tm)) s2)
        (ren_tm xi_tm s3)
  | tNat => tNat
  | tTT => tTT
  | tSeq s0 s1 s2 => tSeq s0 (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | tUnit => tUnit
  end.

Lemma up_tm_tm (sigma : nat -> tm) : nat -> tm.
Proof.
exact (scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm (sigma_tm : nat -> tm) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => sigma_tm s0
  | tAbs s0 s1 => tAbs s0 (subst_tm (up_tm_tm sigma_tm) s1)
  | tApp s0 s1 s2 => tApp (subst_tm sigma_tm s0) s1 (subst_tm sigma_tm s2)
  | tPi s0 s1 s2 =>
      tPi s0 (subst_tm sigma_tm s1) (subst_tm (up_tm_tm sigma_tm) s2)
  | tUniv s0 => tUniv s0
  | tVoid => tVoid
  | tAbsurd s0 => tAbsurd (subst_tm sigma_tm s0)
  | tEq s0 s1 s2 => tEq s0 (subst_tm sigma_tm s1) (subst_tm sigma_tm s2)
  | tJ s0 s1 s2 => tJ s0 (subst_tm sigma_tm s1) (subst_tm sigma_tm s2)
  | tRefl => tRefl
  | tSig s0 s1 s2 =>
      tSig s0 (subst_tm sigma_tm s1) (subst_tm (up_tm_tm sigma_tm) s2)
  | tPack s0 s1 s2 => tPack s0 (subst_tm sigma_tm s1) (subst_tm sigma_tm s2)
  | tLet s0 s1 s2 s3 =>
      tLet s0 s1 (subst_tm sigma_tm s2)
        (subst_tm (up_tm_tm (up_tm_tm sigma_tm)) s3)
  | tZero => tZero
  | tSuc s0 => tSuc (subst_tm sigma_tm s0)
  | tInd s0 s1 s2 s3 =>
      tInd s0 (subst_tm sigma_tm s1)
        (subst_tm (up_tm_tm (up_tm_tm sigma_tm)) s2) (subst_tm sigma_tm s3)
  | tNat => tNat
  | tTT => tTT
  | tSeq s0 s1 s2 => tSeq s0 (subst_tm sigma_tm s1) (subst_tm sigma_tm s2)
  | tUnit => tUnit
  end.

Lemma upId_tm_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = var_tm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_tm (sigma_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s return subst_tm sigma_tm s = s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | tApp s0 s1 s2 =>
      congr_tApp (idSubst_tm sigma_tm Eq_tm s0) (eq_refl s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 => congr_tAbsurd (idSubst_tm sigma_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1) (idSubst_tm sigma_tm Eq_tm s2)
        (idSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upId_tm_tm _ (upId_tm_tm _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (idSubst_tm sigma_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upId_tm_tm _ (upId_tm_tm _ Eq_tm)) s2)
        (idSubst_tm sigma_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0) (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma upExtRen_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm) {struct s} :
ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s return ren_tm xi_tm s = ren_tm zeta_tm s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | tApp s0 s1 s2 =>
      congr_tApp (extRen_tm xi_tm zeta_tm Eq_tm s0) (eq_refl s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0) (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 => congr_tAbsurd (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0) (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0) (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0) (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0) (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
        (extRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upExtRen_tm_tm _ _ (upExtRen_tm_tm _ _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0) (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upExtRen_tm_tm _ _ (upExtRen_tm_tm _ _ Eq_tm)) s2)
        (extRen_tm xi_tm zeta_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0) (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma upExt_tm_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s return subst_tm sigma_tm s = subst_tm tau_tm s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | tApp s0 s1 s2 =>
      congr_tApp (ext_tm sigma_tm tau_tm Eq_tm s0) (eq_refl s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0) (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 => congr_tAbsurd (ext_tm sigma_tm tau_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0) (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0) (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0) (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0) (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
        (ext_tm (up_tm_tm (up_tm_tm sigma_tm)) (up_tm_tm (up_tm_tm tau_tm))
           (upExt_tm_tm _ _ (upExt_tm_tm _ _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (ext_tm sigma_tm tau_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0) (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm (up_tm_tm (up_tm_tm sigma_tm)) (up_tm_tm (up_tm_tm tau_tm))
           (upExt_tm_tm _ _ (upExt_tm_tm _ _ Eq_tm)) s2)
        (ext_tm sigma_tm tau_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0) (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma up_ren_ren_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(rho_tm : nat -> nat) (Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x)
(s : tm) {struct s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | tApp s0 s1 s2 =>
      congr_tApp (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0) (eq_refl s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0) (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 => congr_tAbsurd (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0) (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0) (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0) (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0) (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
        (compRenRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upRen_tm_tm (upRen_tm_tm rho_tm))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0) (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upRen_tm_tm (upRen_tm_tm rho_tm))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_tm)) s2)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0) (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma up_ren_subst_tm_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm) {struct s} :
subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s return subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | tApp s0 s1 s2 =>
      congr_tApp (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (eq_refl s1) (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0) (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 =>
      congr_tAbsurd (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0) (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0) (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
        (compRenSubst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_ren_subst_tm_tm _ _ _ (up_ren_subst_tm_tm _ _ _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_ren_subst_tm_tm _ _ _ (up_ren_subst_tm_tm _ _ _ Eq_tm)) s2)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma up_subst_ren_tm_tm (sigma : nat -> tm) (zeta_tm : nat -> nat)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x) 
(s : tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s return ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | tApp s0 s1 s2 =>
      congr_tApp (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (eq_refl s1) (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 =>
      congr_tAbsurd (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
        (compSubstRen_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_ren_tm_tm _ _ _ (up_subst_ren_tm_tm _ _ _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 =>
      congr_tSuc (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_ren_tm_tm _ _ _ (up_subst_ren_tm_tm _ _ _ Eq_tm)) s2)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma up_subst_subst_tm_tm (sigma : nat -> tm) (tau_tm : nat -> tm)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s return subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | tApp s0 s1 s2 =>
      congr_tApp (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (eq_refl s1) (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 =>
      congr_tAbsurd (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
        (compSubstSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_subst_tm_tm _ _ _ (up_subst_subst_tm_tm _ _ _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 =>
      congr_tSuc (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_subst_tm_tm _ _ _ (up_subst_subst_tm_tm _ _ _ Eq_tm)) s2)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma renRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise (xi_tm : nat -> nat) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise (xi_tm : nat -> nat) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise (sigma_tm : nat -> tm) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_tm : nat -> nat) (sigma_tm : nat -> tm)
(Eq_tm : forall x, funcomp (var_tm) xi_tm x = sigma_tm x) (s : tm) {struct s}
   :
ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s return ren_tm xi_tm s = subst_tm sigma_tm s with
  | var_tm s0 => Eq_tm s0
  | tAbs s0 s1 =>
      congr_tAbs (eq_refl s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | tApp s0 s1 s2 =>
      congr_tApp (rinst_inst_tm xi_tm sigma_tm Eq_tm s0) (eq_refl s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tPi s0 s1 s2 =>
      congr_tPi (eq_refl s0) (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s2)
  | tUniv s0 => congr_tUniv (eq_refl s0)
  | tVoid => congr_tVoid
  | tAbsurd s0 => congr_tAbsurd (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | tEq s0 s1 s2 =>
      congr_tEq (eq_refl s0) (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tJ s0 s1 s2 =>
      congr_tJ (eq_refl s0) (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tRefl => congr_tRefl
  | tSig s0 s1 s2 =>
      congr_tSig (eq_refl s0) (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s2)
  | tPack s0 s1 s2 =>
      congr_tPack (eq_refl s0) (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tLet s0 s1 s2 s3 =>
      congr_tLet (eq_refl s0) (eq_refl s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
        (rinst_inst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm sigma_tm))
           (rinstInst_up_tm_tm _ _ (rinstInst_up_tm_tm _ _ Eq_tm)) s3)
  | tZero => congr_tZero
  | tSuc s0 => congr_tSuc (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | tInd s0 s1 s2 s3 =>
      congr_tInd (eq_refl s0) (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm sigma_tm))
           (rinstInst_up_tm_tm _ _ (rinstInst_up_tm_tm _ _ Eq_tm)) s2)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s3)
  | tNat => congr_tNat
  | tTT => congr_tTT
  | tSeq s0 s1 s2 =>
      congr_tSeq (eq_refl s0) (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | tUnit => congr_tUnit
  end.

Lemma rinstInst'_tm (xi_tm : nat -> nat) (s : tm) :
  ren_tm xi_tm s = subst_tm (funcomp (var_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (ren_tm xi_tm) (subst_tm (funcomp (var_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_tm) s = s.
Proof.
exact (idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise : pointwise_relation _ eq (subst_tm (var_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise : pointwise_relation _ eq (@ren_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm (sigma_tm : nat -> tm) (x : nat) :
  subst_tm sigma_tm (var_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise (sigma_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm)) sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm (xi_tm : nat -> nat) (x : nat) :
  ren_tm xi_tm (var_tm x) = var_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm))
    (funcomp (var_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

#[global] Instance Subst_tm : (Subst1 _ _ _) := @subst_tm.

#[global] Instance Up_tm_tm : (Up_tm _ _) := @up_tm_tm.

#[global] Instance Ren_tm : (Ren1 _ _ _) := @ren_tm.

#[global]
Instance VarInstance_tm : (Var _ _) := @var_tm.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing)  : subst_scope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing)  : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
( at level 5, format "x __tm", only printing)  : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm")  :
subst_scope.

#[global]
Instance subst_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => ext_tm f_tm g_tm Eq_tm s).
Qed.

#[global]
Instance ren_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance ren_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => extRen_tm f_tm g_tm Eq_tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                      Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_tm, Var, ids,
                                            Ren_tm, Ren1, ren1, Up_tm_tm,
                                            Up_tm, up_tm, Subst_tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress unfold up_tm_tm, upRen_tm_tm, up_ren
                 | progress cbn[subst_tm ren_tm]
                 | progress fsimpl ]).

Ltac asimpl :=
                repeat
                 unfold VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_tm: rewrite.

#[global] Hint Opaque ren_tm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.


(* Backwards compatibility with the old as2-exe-generated header. *)
Notation fin := nat (only parsing).

(* Bring the autosubst-generated [.:], shift, and other helper notations
   into scope. Without this they live inside the [UnscopedNotations] module
   and cannot be seen by the proofs. *)
Include UnscopedNotations.

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

Global Disable Notation "'var'" : subst_scope.
Global Disable Notation "↑".
Global Open Scope subst_scope.

End syntax_sig.
