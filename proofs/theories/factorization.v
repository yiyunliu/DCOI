Require Import imports syntax par normalform.

Module Type factorization_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import normalform : normalform_sig lattice syntax par).

(* Weak head reduction *)
Inductive HRed : tm -> tm -> Prop :=
(* | HR_Pi0 ℓ0 A0 A1 B : *)
(*   HRed A0 A1 -> *)
(*   (* --------------------- *) *)
(*   HRed (tPi ℓ0 A0 B) (tPi ℓ0 A1 B) *)

(* | HR_Pi1 ℓ0 A B0 B1 : *)
(*   nf A -> *)
(*   HRed B0 B1  -> *)
(*   (* --------------------- *) *)
(*   HRed (tPi ℓ0 A B0) (tPi ℓ0 A B1) *)

| HR_App a0 a1 ℓ0 b :
  HRed a0 a1 ->
  (* ------------------------- *)
  HRed (tApp a0 ℓ0 b) (tApp a1 ℓ0 b)

| HR_AppAbs a b ℓ0 :
  (* ---------------------------- *)
  HRed (tApp (tAbs ℓ0 a) ℓ0 b) (a [b..])

(* | HR_Absurd a b : *)
(*   HRed a b -> *)
(*   (* ---------- *) *)
(*   HRed (tAbsurd a) (tAbsurd b) *)

(* | HR_Eq0 ℓ0 a0 a1 b A : *)
(*   HRed a0 a1 -> *)
(*   (* ---------- *) *)
(*   HRed (tEq ℓ0 a0 b A) (tEq ℓ0 a1 b A) *)

(* | HR_Eq1 ℓ0 a b0 b1 A : *)
(*   nf a -> *)
(*   HRed b0 b1 -> *)
(*   (* ---------- *) *)
(*   HRed (tEq ℓ0 a b0 A) (tEq ℓ0 a b1 A) *)

(* | HR_Eq2 ℓ0 a b A0 A1 : *)
(*   nf a -> *)
(*   nf b -> *)
(*   HRed A0 A1 -> *)
(*   (* ---------- *) *)
(*   HRed (tEq ℓ0 a b A0) (tEq ℓ0 a b A1) *)

| HR_J ℓp  t p0 p1 :
  HRed p0 p1 ->
  (* ---------- *)
  HRed (tJ ℓp t p0) (tJ ℓp t p1)

| HR_JRefl ℓp t :
  (* ---------- *)
  HRed (tJ ℓp t tRefl) t

(* | HR_Sig0 ℓ0 A0 A1 B : *)
(*   HRed A0 A1 -> *)
(*   (* --------------------- *) *)
(*   HRed (tSig ℓ0 A0 B) (tSig ℓ0 A1 B) *)

(* | HR_Sig1 ℓ0 A B0 B1 : *)
(*   nf A -> *)
(*   HRed B0 B1  -> *)
(*   (* --------------------- *) *)
(*   HRed (tSig ℓ0 A B0) (tSig ℓ0 A B1) *)

| HR_Let ℓ0 ℓ1 a0 a1 b :
  HRed a0 a1 ->
  (* --------------------- *)
  HRed (tLet ℓ0 ℓ1 a0 b) (tLet ℓ0 ℓ1 a1 b)

| HR_LetPack ℓ0 ℓ1 a b c :
  HRed (tLet ℓ0 ℓ1 (tPack ℓ0 a b) c) c[b .: a ..]

| HR_Down ℓ0 p0 p1 :
  HRed p0 p1 ->
  HRed (tDown ℓ0 p0) (tDown ℓ0 p1)

| HR_DownRefl ℓ0 :
  HRed (tDown ℓ0 tRefl) tRefl.

(* Non-essential parallel reduction *)
(* Reduces the parts that are not reduced by weak head reduction *)
Inductive NPar : tm -> tm -> Prop :=
| NP_Var i :
  (* ------- *)
  NPar (var_tm i) (var_tm i)

| NP_Univ n :
  (* -------- *)
  NPar (tUniv n) (tUniv n)

| NP_Pi ℓ0 A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->
  (* --------------------- *)
  NPar (tPi ℓ0 A0 B0) (tPi ℓ0 A1 B1)

| NP_Abs ℓ0 a0 a1 :
  (a0 ⇒ a1) ->
  (* -------------------- *)
  NPar (tAbs ℓ0 a0) (tAbs ℓ0 a1)

| NP_App a0 a1 ℓ0 b0 b1 :
  NPar a0 a1 ->
  (b0 ⇒ b1) ->
  (* ------------------------- *)
  NPar (tApp a0 ℓ0 b0) (tApp a1 ℓ0 b1)

| NP_Absurd a b :
  a ⇒ b ->
  (* ---------- *)
  NPar (tAbsurd a) (tAbsurd b)

| NP_Eq ℓ0 a0 b0 A0 a1 b1 A1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (A0 ⇒ A1) ->
  (* ---------- *)
  NPar (tEq ℓ0 a0 b0 A0) (tEq ℓ0 a1 b1 A1)

| NP_J ℓp t0 p0 t1 p1 :
  (t0 ⇒ t1) ->
  NPar p0 p1 ->
  (* ---------- *)
  NPar (tJ ℓp t0 p0) (tJ ℓp t1 p1)

| NP_Sig ℓ A0 A1 B0 B1 :
  (A0 ⇒ A1) ->
  (B0 ⇒ B1) ->
  (* --------------------- *)
  NPar (tSig ℓ A0 B0) (tSig ℓ A1 B1)

| NP_Pack ℓ a0 a1 b0 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (* ------------------------- *)
  NPar (tPack ℓ a0 b0) (tPack ℓ a1 b1)

| NP_Let ℓ0 ℓ1 a0 b0 a1 b1 :
  NPar a0 a1 ->
  b0 ⇒ b1 ->
  (* --------------------- *)
  NPar (tLet ℓ0 ℓ1 a0 b0) (tLet ℓ0 ℓ1 a1 b1)

| NP_Down ℓ0 p0 p1 :
  NPar p0 p1 ->
  (* ------------------------------ *)
  NPar (tDown ℓ0 p0) (tDown ℓ0 p1)

| NP_Void :
  NPar tVoid tVoid

| NP_Refl :
  NPar tRefl tRefl

| NP_D :
  NPar tD tD.



Module pfacts := par_facts lattice syntax par.
Import pfacts.

Lemma NPar_Par a b : NPar a b -> a ⇒ b.
Proof. induction 1; hauto lq:on ctrs:Par. Qed.

Lemma NPar_renaming a b :
  NPar a b ->
  forall ξ, NPar (ren_tm ξ a) (ren_tm ξ b).
Proof.
  move => h.
  elim:a b/h; hauto lq:on ctrs:NPar use:Par_renaming.
Qed.

Lemma HR_AppAbs' a ℓ0 b u :
  u = subst_tm (b..) a ->
  HRed (tApp (tAbs ℓ0 a) ℓ0 b) u.
Proof. move => ->. by apply HR_AppAbs. Qed.

Lemma HR_LetPack' ℓ0 ℓ1 a b c u :
  u = c[b .: a ..] ->
  HRed (tLet ℓ0 ℓ1 (tPack ℓ0 a b) c) u.
Proof. move => ->. by apply HR_LetPack. Qed.

Lemma HRed_renaming a b (h : HRed a b) :
  forall ξ, HRed (ren_tm ξ a) (ren_tm ξ b).
Proof.
  elim:a b/h; try qauto ctrs:HRed.
  - move => *; apply : HR_AppAbs'; by asimpl.
  - move => *; apply : HR_LetPack'; by asimpl.
Qed.

Lemma merge t a u :
  NPar t a ->
  HRed a u ->
  t ⇒ u.
Proof.
  move => h. move : u. elim:t a/h;
    qauto ctrs:Par inv:HRed, NPar use:NPar_Par.
Qed.

(* Takahashi's *-sequence *)
Inductive starseq : tm -> tm -> Prop :=
| S_Refl M N :
  NPar M N ->
  (* ------- *)
  starseq M N
| S_Step M P N :
  HRed M P ->
  M ⇒ N ->
  starseq P N ->
  starseq M N.

Lemma starseq_par a b :
  starseq a b ->
  a ⇒ b.
Proof. induction 1; sfirstorder use:NPar_Par. Qed.

Lemma starseq_renaming ξ a b :
  starseq a b ->
  starseq (ren_tm ξ a) (ren_tm ξ b).
Proof.
  move => h.
  elim : a b /h;
    hauto lq:on ctrs:starseq use:NPar_renaming, Par_renaming, HRed_renaming.
Qed.

Lemma starseq_abs_cong ℓ M N
  (h : starseq M N) :
  starseq (tAbs ℓ M) (tAbs ℓ N).
Proof.
  apply S_Refl.
  hauto lq:on ctrs:NPar use:starseq_par.
Qed.

Lemma starseq_app_cong M N ℓ P Q :
  starseq M N ->
  P ⇒ Q ->
  starseq (tApp M ℓ P) (tApp N ℓ Q).
Proof.
  move => h. move : P Q ℓ. elim : M N / h.
  - sfirstorder use:S_Refl, NP_App.
  - hauto lq:on ctrs:starseq, NPar, Par, HRed.
Qed.

Lemma starseq_down_cong ℓ0 a b :
  starseq a b ->
  starseq (tDown ℓ0 a) (tDown ℓ0 b).
Proof.
  move => h. elim : a b /h; hauto lq:on ctrs:starseq, NPar,Par,HRed.
Qed.

Lemma starseq_let_cong ℓ0 ℓ1 a0 a1 b0 b1 :
  starseq a0 a1 ->
  b0 ⇒ b1 ->
  starseq (tLet ℓ0 ℓ1 a0 b0) (tLet ℓ0 ℓ1 a1 b1).
Proof.
  move => h. move : ℓ0 ℓ1 b0 b1. elim : a0 a1/h; hauto lq:on ctrs:starseq, NPar,Par,HRed.
Qed.

Lemma starseq_j_cong ℓp t0 t1 p0 p1 :
  t0 ⇒ t1 ->
  starseq p0 p1 ->
  starseq (tJ ℓp t0 p0) (tJ ℓp t1 p1).
Proof.
  move => h h0.
  elim : p0 p1 /h0; hauto lq:on ctrs:starseq, NPar,Par,HRed.
Qed.

Lemma starseq_ρ_par ρ0 ρ1 :
  (forall i : fin, starseq (ρ0 i) (ρ1 i)) ->
  (forall i : fin, Par (ρ0 i) (ρ1 i)).
Proof. firstorder using starseq_par. Qed.

Lemma ipar_starseq_morphing :
  forall M N : tm,
  M ⇒ N ->
  forall ρ0 ρ1 : fin -> tm,
    (forall i : fin, starseq (ρ0 i) (ρ1 i)) -> starseq (subst_tm ρ0 M) (subst_tm ρ1 N).
Proof.
  move => M N h. elim : M N / h.
  - sfirstorder.
  - hauto l:on.
  - move => ℓ0 A0 A1 B0 B1 ???? ρ0 ρ1 /starseq_ρ_par ?.
    apply S_Refl.
    suff : Par (tPi ℓ0 A0 B0)[ρ0] (tPi ℓ0 A1 B1)[ρ1] by hauto lq:on ctrs:NPar inv:Par.
    hauto lq:on use:Par_morphing, Par unfold:Par_m.
  - move => ℓ0 a0 a1 ha iha ρ0 ρ1 /starseq_ρ_par ?.
    apply S_Refl.
    suff : Par (tAbs ℓ0 a0)[ρ0] (tAbs ℓ0 a1)[ρ1] by hauto lq:on ctrs:NPar inv:Par.
    hauto lq:on use:Par_morphing, Par unfold:Par_m.
  - move => a0 a1 ℓ0 b0 b1 ha iha hb ihb ρ0 ρ1 hρ /=.
    apply starseq_app_cong.
    sfirstorder.
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par.
  - move => a0 a1 b0 b1 ℓ0 ha iha hb ihb ρ0 ρ1 h /=.
    apply : S_Step.
    by apply HR_AppAbs.
    apply P_AppAbs' with (a0 := subst_tm (up_tm_tm ρ1) a1) (b1 := subst_tm ρ1 b1).
    by asimpl.
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par, Par_morphing_lift unfold:Par_m.
    (* par cong *)
    sfirstorder use:Par_morphing, starseq_ρ_par, Par_morphing_lift unfold:Par_m.
    asimpl.
    apply iha.
    case => //=.
    by apply ihb.
  - hauto l:on.
  - hauto q:on ctrs:NPar use:Par_morphing, starseq_ρ_par, S_Refl unfold:Par_m.
  - hauto l:on.
  - hauto q:on ctrs:NPar use:Par_morphing, starseq_ρ_par, S_Refl unfold:Par_m.
  - hauto q:on use:Par_morphing, starseq_ρ_par, starseq_j_cong unfold:Par_m.
  - move => ℓp t0 t1 ht iht ρ0 ρ1 hρ /=.
    apply : S_Step.
    apply HR_JRefl.
    move/starseq_ρ_par : (hρ) => ?.
    hauto lq:on ctrs:Par use:Par_morphing.
    hauto l:on.
  - move => ℓ0 A0 A1 B0 B1 ???? ρ0 ρ1 /starseq_ρ_par ?.
    apply S_Refl.
    suff : Par (tSig ℓ0 A0 B0)[ρ0] (tSig ℓ0 A1 B1)[ρ1] by hauto lq:on ctrs:NPar inv:Par.
    hauto lq:on use:Par_morphing, Par unfold:Par_m.
  - move => ℓ0 A0 A1 B0 B1 ???? ρ0 ρ1 /starseq_ρ_par ?.
    apply S_Refl.
    suff : Par (tPack ℓ0 A0 B0)[ρ0] (tPack ℓ0 A1 B1)[ρ1] by hauto lq:on ctrs:NPar inv:Par.
    hauto lq:on use:Par_morphing, Par unfold:Par_m.
  - hauto q:on use:Par_morphing_lift2, starseq_ρ_par, Par_morphing, starseq_let_cong unfold:Par_m.
  - move => ℓ0 ℓ1 a0 b0 c0 a1 b1 c1 ha iha hb ihb hc ihc ρ0 ρ1 hρ /=.
    apply : S_Step.
    apply HR_LetPack.
    apply P_LetPack' with (a1 := a1[ρ1]) (b1 := b1[ρ1]) (c1 := c1 [up_tm_tm (up_tm_tm ρ1) ]).
    by asimpl.
    sfirstorder use:Par_morphing, starseq_ρ_par unfold:Par_m.
    sfirstorder use:Par_morphing, starseq_ρ_par unfold:Par_m.
    sfirstorder use:Par_morphing, starseq_ρ_par, Par_morphing_lift2 unfold:Par_m.
    asimpl.
    apply ihc.
    case => //=. hauto l:on.
    case => //=. hauto l:on.
  - hauto l:on.
  - eauto using starseq_down_cong.
  - hauto lq:on ctrs:starseq, HRed, Par, NPar.
Qed.

Lemma split t s (h : t ⇒ s) :
  starseq t s.
Proof.
  elim : t s /h ; try hauto q:on ctrs:NPar, starseq.
  - eauto using starseq_app_cong.
  - move => *.
    apply : S_Step.
    by apply HR_AppAbs.
    by apply P_AppAbs.
    hauto lq:on ctrs:starseq inv:nat use:ipar_starseq_morphing.
  - eauto using starseq_j_cong.
  - move => *.
    apply : S_Step=>//.
    by apply HR_JRefl.
    by apply P_JRefl.
    exact.
  - eauto using starseq_let_cong.
  - move => *.
    apply : S_Step=>//.
    by apply HR_LetPack.
    by apply P_LetPack.
    hauto lq:on ctrs:starseq inv:nat use:ipar_starseq_morphing.
  - eauto using starseq_down_cong.
  - hauto lq:on ctrs:NPar,Par,starseq,HRed.
Qed.

(* Erase the information about one step par from starseq *)
Lemma starseq_erase a b (h : starseq a b) :
  exists u, rtc HRed a u /\ NPar u b.
Proof.
  elim : a b /h; hauto lq:on ctrs:rtc.
Qed.

Lemma local_postponement t a u  :
  NPar t a ->
  HRed a u ->
  exists q, rtc HRed t q /\ NPar q u.
Proof. sfirstorder use:split, merge, starseq_erase. Qed.

End factorization_sig.
