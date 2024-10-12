Require Import imports syntax par normalform.

(* A simplified standardization proof based on the proof by Takahashi *)
Module Type factorization_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import normalform : normalform_sig lattice syntax par).

(* Weak head reduction *)
Inductive HRed : tm -> tm -> Prop :=
| HR_App a0 a1 ℓ0 b :
  HRed a0 a1 ->
  (* ------------------------- *)
  HRed (tApp a0 ℓ0 b) (tApp a1 ℓ0 b)

| HR_AppAbs a b ℓ0 :
  (* ---------------------------- *)
  HRed (tApp (tAbs ℓ0 a) ℓ0 b) (a [b..])

| HR_J ℓp  t p0 p1 :
  HRed p0 p1 ->
  (* ---------- *)
  HRed (tJ ℓp t p0) (tJ ℓp t p1)

| HR_JRefl ℓp t :
  (* ---------- *)
  HRed (tJ ℓp t tRefl) t

| HR_Let ℓ0 ℓ1 a0 a1 b :
  HRed a0 a1 ->
  (* --------------------- *)
  HRed (tLet ℓ0 ℓ1 a0 b) (tLet ℓ0 ℓ1 a1 b)

| HR_LetPack ℓ0 ℓ1 a b c :
  HRed (tLet ℓ0 ℓ1 (tPack ℓ0 a b) c) c[b .: a ..]

| HR_Ind ℓ a b c0 c1 :
  HRed c0 c1 ->
  (* ------------------------ *)
  HRed (tInd ℓ a b c0) (tInd ℓ a b c1)

| HR_IndZero ℓ a b :
  (* ------------------------ *)
  HRed (tInd ℓ a b tZero) a

| HR_IndSuc ℓ a b c:
  (* ------------------------ *)
  HRed (tInd ℓ a b (tSuc c)) b[(tInd ℓ a b c) .: c ..]

| HR_Seq ℓ a0 a1 b :
  HRed a0 a1 ->
  (* -------------------- *)
  HRed (tSeq ℓ a0 b) (tSeq ℓ a1 b)

| HR_SeqTT ℓ b :
  (* -------------------- *)
  HRed (tSeq ℓ tTT b) b.

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

| NP_Eq ℓ0 a0 b0 a1 b1 :
  (a0 ⇒ a1) ->
  (b0 ⇒ b1) ->
  (* ---------- *)
  NPar (tEq ℓ0 a0 b0) (tEq ℓ0 a1 b1)

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

| NP_Void :
  NPar tVoid tVoid

| NP_Refl :
  NPar tRefl tRefl

| NP_Nat :
  NPar tNat tNat

| NP_Zero :
  NPar tZero tZero

| NP_Suc a b :
  a ⇒ b ->
  (* ---------------- *)
  NPar (tSuc a) (tSuc b)

| NP_Ind ℓ a0 b0 c0 a1 b1 c1  :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  NPar c0 c1 ->
  (* ----------- *)
  NPar (tInd ℓ a0 b0 c0) (tInd ℓ a1 b1 c1)

| NP_TT :
  NPar tTT tTT

| NP_Unit :
  NPar tUnit tUnit

| NP_Seq ℓ a0 a1 b0 b1 :
  NPar a0 a1 ->
  b0 ⇒ b1 ->
  NPar (tSeq ℓ a0 b0) (tSeq ℓ a1 b1).

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

Lemma HR_IndSuc' ℓ a b c u:
  u = b[(tInd ℓ a b c) .: c ..] ->
  (* ------------------------ *)
  HRed (tInd ℓ a b (tSuc c)) u.
Proof. move => ->. by apply HR_IndSuc. Qed.

Lemma HRed_renaming a b (h : HRed a b) :
  forall ξ, HRed (ren_tm ξ a) (ren_tm ξ b).
Proof.
  elim:a b/h; try qauto ctrs:HRed.
  - move => *; apply : HR_AppAbs'; by asimpl.
  - move => *; apply : HR_LetPack'; by asimpl.
  - move => *; apply : HR_IndSuc'; by asimpl.
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

Lemma starseq_suc_cong M N
  (h : starseq M N) :
  starseq (tSuc M) (tSuc N).
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

Lemma starseq_ind_cong ℓ a0 a1 b0 b1 c0 c1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  starseq c0 c1 ->
  starseq (tInd ℓ a0 b0 c0) (tInd ℓ a1 b1 c1).
Proof.
  move => h0 h1 h2.
  elim : c0 c1 /h2; hauto lq:on ctrs:starseq, NPar,Par,HRed.
Qed.

Lemma starseq_seq_cong ℓ a0 a1 b0 b1 :
  starseq a0 a1 ->
  b0 ⇒ b1 ->
  starseq (tSeq ℓ a0 b0) (tSeq ℓ a1 b1).
Proof.
  move => h.
  elim : a0 a1 /h; hauto lq:on ctrs:starseq, NPar,Par,HRed.
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
    sfirstorder use:Par_morphing, starseq_ρ_par.
  - move => a0 a1 b0 b1 ℓ0 ha iha hb ihb ρ0 ρ1 h /=.
    apply : S_Step.
    by apply HR_AppAbs.
    apply P_AppAbs' with (a0 := subst_tm (up_tm_tm ρ1) a1) (b1 := subst_tm ρ1 b1).
    by asimpl.
    sfirstorder use:Par_morphing, starseq_ρ_par, Par_morphing_lift unfold:Par_m.
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
  - eauto using starseq_suc_cong.
  - move => ℓ a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc ρ0 ρ1 hρ /=.
    move/starseq_ρ_par : (hρ) => ?.
    apply starseq_ind_cong; eauto.
    hauto lq:on ctrs:Par use:Par_morphing unfold:Par_m.
    hauto lq:on ctrs:Par use:Par_morphing, Par_morphing_lift2 unfold:Par_m.
  - move => ℓ a0 a1 b ha iha ρ0 ρ1 hρ /=.
    apply : S_Step; eauto.
    apply HR_IndZero.
    apply P_IndZero.
    sfirstorder use:Par_morphing, starseq_ρ_par unfold:Par_m.
  - move => ℓ a0 a1 b0 b1 c0 c1 ha iha hb ihb hc ihc ρ0 ρ1 hρ.
    move/starseq_ρ_par : (hρ) => ?.
    apply S_Step with (P := b0[(tInd ℓ a0 b0 c0).: c0 ..][ρ0]).
    apply : HR_IndSuc'. rewrite-/subst_tm; by asimpl.
    apply Par_morphing. hauto l:on use:starseq_ρ_par unfold:Par_m.
    by apply P_IndSuc.
    asimpl.
    apply ihb.
    case => //=.
    apply starseq_ind_cong ; eauto. hauto l:on use:Par_morphing unfold:Par_m.
    suff : b0[up_tm_tm (up_tm_tm ρ0)] ⇒ b1[up_tm_tm (up_tm_tm ρ1)] by asimpl.
    sfirstorder use:Par_morphing_lift2, Par_morphing unfold:Par_m.
    case => //=; eauto.
  - hauto l:on.
  - hauto l:on.
  - hauto q:on use:starseq_ρ_par, Par_morphing, starseq_seq_cong unfold:Par_m.
  - move => ℓ b0 b1 hb ihb ρ0 ρ1 hρ /=.
    eapply S_Step.
    apply HR_SeqTT.
    apply P_SeqTT.
    sfirstorder use:Par_morphing, starseq_ρ_par unfold:Par_m.
    by eauto.
  - hauto l:on.
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
  - eauto using starseq_ind_cong.
  - hauto lq:on ctrs:starseq, HRed, Par.
  - move => *.
    apply : S_Step=>//.
    by apply HR_IndSuc.
    by apply P_IndSuc.
    apply : ipar_starseq_morphing; eauto.
    case => //=.
    sfirstorder use:starseq_ind_cong.
    case => //=. move => n. apply S_Refl. apply NP_Var.
  - eauto using starseq_seq_cong.
  - move => ℓ b0 b1 hb ihb.
    apply : S_Step.
    apply HR_SeqTT.
    by apply P_SeqTT.
    exact.
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

Lemma local_postponement_star t a u :
  NPar t a ->
  rtc HRed a u ->
  exists q, rtc HRed t q /\ NPar q u.
  move => + h. move : t. elim : a u / h.
  sfirstorder.
  qauto l:on ctrs:rtc use:local_postponement, rtc_transitive.
Qed.

Lemma factorization t u :
  rtc Par t u ->
  exists v, rtc HRed t v /\ rtc NPar v u.
Proof.
  move => h. elim:t u/h=>//=.
  - hauto lq:on ctrs:rtc.
  - move => a b c ha hb [v][ihb0]ihb1.
    move /split /starseq_erase : ha.
    move => [u][hu0]hu1.
    move : local_postponement_star ihb0 hu1; repeat move/[apply].
    move => [q][hq0]hq1.
    exists q. hauto lq:on ctrs:rtc use:rtc_transitive.
Qed.

Definition isAbs a :=
  match a with
  | tAbs _ _ => true
  | _ => false
  end.

Definition isPack a :=
  match a with
  | tPack _ _ _ => true
  | _ => false
  end.

Definition isNum a :=
  match a with
  | tSuc _ => true
  | tZero => true
  | _ => false
  end.

(* Leftmost-outermost reduction *)
Inductive LoRed : tm -> tm -> Prop :=
| LoR_Pi0 ℓ0 A0 A1 B :
  LoRed A0 A1 ->
  (* --------------------- *)
  LoRed (tPi ℓ0 A0 B) (tPi ℓ0 A1 B)

| LoR_Pi1 ℓ0 A B0 B1 :
  nf A ->
  LoRed B0 B1 ->
  (* --------------------- *)
  LoRed (tPi ℓ0 A B0) (tPi ℓ0 A B1)

| LoR_Abs ℓ0 a0 a1 :
  LoRed a0 a1 ->
  (* -------------------- *)
  LoRed (tAbs ℓ0 a0) (tAbs ℓ0 a1)

| LoR_App0 a0 a1 ℓ0 b :
  ~~ isAbs a0 ->
  LoRed a0 a1 ->
  (* ------------------------- *)
  LoRed (tApp a0 ℓ0 b) (tApp a1 ℓ0 b)

| LoR_App1 a ℓ0 b0 b1 :
  ne a ->
  LoRed b0 b1 ->
  (* ------------------------- *)
  LoRed (tApp a ℓ0 b0) (tApp a ℓ0 b1)

| LoR_AppAbs a b ℓ :
  (* ---------------------------- *)
  LoRed (tApp (tAbs ℓ a) ℓ b) (a [b..])

| LoR_Absurd a b :
  LoRed a b ->
  (* ---------- *)
  LoRed (tAbsurd a) (tAbsurd b)

| LoR_Eq0 ℓ0 a0 a1 b :
  LoRed a0 a1 ->
  (* ---------- *)
  LoRed (tEq ℓ0 a0 b) (tEq ℓ0 a1 b)

| LoR_Eq1 ℓ0 a b0 b1 :
  nf a ->
  LoRed b0 b1 ->
  (* ---------- *)
  LoRed (tEq ℓ0 a b0) (tEq ℓ0 a b1)

| LoR_J0 ℓp t p0 p1 :
  LoRed p0 p1 ->
  (* ---------- *)
  LoRed (tJ ℓp t p0) (tJ ℓp t p1)

| LoR_J1 ℓp t0 t1 p :
  ne p ->
  LoRed t0 t1 ->
  (* ---------- *)
  LoRed (tJ ℓp t0 p) (tJ ℓp t1 p)

| LoR_JRefl ℓp t :
  (* ---------- *)
  LoRed (tJ ℓp t tRefl) t

| LoR_Sig0 ℓ0 A0 A1 B :
  LoRed A0 A1 ->
  (* --------------------- *)
  LoRed (tSig ℓ0 A0 B) (tSig ℓ0 A1 B)

| LoR_Sig1 ℓ0 A B0 B1 :
  nf A ->
  LoRed B0 B1 ->
  (* --------------------- *)
  LoRed (tSig ℓ0 A B0) (tSig ℓ0 A B1)

| LoR_Pack0 ℓ a0 a1 b :
  LoRed a0 a1 ->
  (* ------------------------- *)
  LoRed (tPack ℓ a0 b) (tPack ℓ a1 b)

| LoR_Pack1 ℓ a b0 b1 :
  nf a ->
  LoRed b0 b1 ->
  (* ------------------------- *)
  LoRed (tPack ℓ a b0) (tPack ℓ a b1)

| LoR_Let0 ℓ0 ℓ1 a0 a1 b :
  ~~ isPack a0 ->
  LoRed a0 a1 ->
  (* --------------------- *)
  LoRed (tLet ℓ0 ℓ1 a0 b) (tLet ℓ0 ℓ1 a1 b)

| LoR_Let1 ℓ0 ℓ1 a b0 b1 :
  ne a ->
  LoRed b0 b1 ->
  (* --------------------- *)
  LoRed (tLet ℓ0 ℓ1 a b0) (tLet ℓ0 ℓ1 a b1)

| LoR_LetPack ℓ0 ℓ1 a b c :
  (* --------------------------------------------- *)
  LoRed (tLet ℓ0 ℓ1 (tPack ℓ0 a b) c) c[b .: a ..]

| LoR_Ind0 ℓ a b c0 c1 :
  ~~ isNum c0 ->
  LoRed c0 c1 ->
  (* --------------------- *)
  LoRed (tInd ℓ a b c0) (tInd ℓ a b c1)

| LoR_Ind1 ℓ a0 a1 b c :
  ne c ->
  LoRed a0 a1 ->
  (* ------------------------- *)
  LoRed (tInd ℓ a0 b c) (tInd ℓ a1 b c)

| LoR_Ind2 ℓ a b0 b1 c :
  ne c ->
  nf a ->
  LoRed b0 b1 ->
  (* ------------------------- *)
  LoRed (tInd ℓ a b0 c) (tInd ℓ a b1 c)

| LoR_IndZero ℓ a b :
  (* ----------------------------- *)
  LoRed (tInd ℓ a b tZero) a

| LoR_IndSuc ℓ a b c :
  (* ----------------------------- *)
  LoRed (tInd ℓ a b (tSuc c)) b[(tInd ℓ a b c) .: c ..]

| LoR_Suc a b:
  LoRed a b ->
  LoRed (tSuc a) (tSuc b)

| LoR_Seq0 ℓ a0 a1 b :
  LoRed a0 a1 ->
  LoRed (tSeq ℓ a0 b) (tSeq ℓ a1 b)

| LoR_Seq1 ℓ a b0 b1 :
  ne a ->
  LoRed b0 b1 ->
  LoRed (tSeq ℓ a b0) (tSeq ℓ a b1)

| LoR_SeqTT ℓ b :
  LoRed (tSeq ℓ tTT b) b.

Module nfact := normalform_fact lattice syntax par normalform.
Import nfact.

Lemma NPar_Var_inv a i :
  rtc NPar a (var_tm i) ->
  a = var_tm i.
Proof.
  move E : (var_tm i) => T h. move : i E.
  elim: a T/h; hauto l:on inv:NPar ctrs:NPar, rtc.
Qed.

Lemma NPar_Abs_inv a ℓ b :
  rtc NPar a (tAbs ℓ b) ->
  exists a0, a = tAbs ℓ a0 /\ rtc Par a0 b.
Proof.
  move E : (tAbs ℓ b) => T h.
  move : ℓ b E.
  elim : a T/h; hauto lq:on ctrs:rtc inv:NPar.
Qed.

Lemma NPar_Suc_inv a b :
  rtc NPar a (tSuc b) ->
  exists a0, a = tSuc a0 /\ rtc Par a0 b.
Proof.
  move E : (tSuc b) => T h.
  move : b E.
  elim : a T/h; hauto lq:on ctrs:rtc inv:NPar.
Qed.

Lemma HRed_LoRed : subrelation HRed LoRed.
Proof. induction 1; hauto lq:on inv:HRed ctrs:LoRed. Qed.

Lemma HReds_LoReds : subrelation (rtc HRed) (rtc LoRed).
Proof. sfirstorder use:relations.rtc_subrel, HRed_LoRed. Qed.

Lemma NPars_Pars : subrelation (rtc NPar) (rtc Par).
Proof. sfirstorder use:relations.rtc_subrel, NPar_Par. Qed.

Lemma LoRed_Abs_Cong a b ℓ :
  rtc LoRed a b ->
  rtc LoRed (tAbs ℓ a) (tAbs ℓ b).
Proof. move => h. elim:a b/h; hauto lq:on ctrs:LoRed, rtc. Qed.

Lemma LoRed_Suc_Cong a b :
  rtc LoRed a b ->
  rtc LoRed (tSuc a) (tSuc b).
Proof. move => h. elim:a b/h; hauto lq:on ctrs:LoRed, rtc. Qed.

Lemma NPar_App_inv u a ℓ0 b :
  rtc NPar u (tApp a ℓ0 b) ->
  exists a0 b0, u = tApp a0 ℓ0 b0 /\ rtc NPar a0 a /\ rtc Par b0 b.
Proof.
  move E : (tApp a ℓ0 b) => T h.
  move : a b E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Seq_inv u ℓ0 a b :
  rtc NPar u (tSeq ℓ0 a b) ->
  exists a0 b0, u = tSeq ℓ0 a0 b0 /\ rtc NPar a0 a /\ rtc Par b0 b.
Proof.
  move E : (tSeq ℓ0 a b) => T h.
  move : a b E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Ind_inv u ℓ a b c :
  rtc NPar u (tInd ℓ a b c) ->
  exists a0 b0 c0, u = tInd ℓ a0 b0 c0 /\ rtc NPar c0 c  /\ rtc Par a0 a /\ rtc Par b0 b.
Proof.
  move E : (tInd ℓ a b c) => T h.
  move : a b c E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Pi_inv u ℓ0 A B :
  rtc NPar u (tPi ℓ0 A B) ->
  exists A0 B0, u = tPi ℓ0 A0 B0 /\ rtc Par A0 A /\ rtc Par B0 B.
Proof.
  move E : (tPi ℓ0 A B) => T h.
  move : A B E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Univ_inv u i :
  rtc NPar u (tUniv i) ->
  u = tUniv i.
Proof.
  move E : (tUniv i) => T h.
  move : i E.
  elim : u T/h; hauto l:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Void_inv u :
  rtc NPar u tVoid ->
  u = tVoid.
Proof.
  move E : tVoid => T h.
  move : E.
  elim : u T/h; hauto l:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Nat_inv u :
  rtc NPar u tNat ->
  u = tNat.
Proof.
  move E : tNat => T h.
  move : E.
  elim : u T/h; hauto l:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Absurd_inv u v:
  rtc NPar u (tAbsurd v) ->
  exists u0, u = tAbsurd u0 /\ rtc Par u0 v.
Proof.
  move E : (tAbsurd v) => T h.
  move : E.
  elim : u T/h.
  hauto lq:on ctrs:rtc.
  move => x y z hx hy /[swap] <- /(_ eq_refl); move => [u0][?]hu0. subst.
  hauto lq:on inv:NPar ctrs:rtc,NPar.
Qed.

Lemma NPar_Eq_inv u ℓ0 a b :
  rtc NPar u (tEq ℓ0 a b) ->
  exists a0 b0, u = tEq ℓ0 a0 b0  /\ rtc Par a0 a /\ rtc Par b0 b.
Proof.
  move E : (tEq ℓ0 a b) => T h.
  move : a b E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_J_inv u ℓ0 t p :
  rtc NPar u (tJ ℓ0 t p) ->
  exists t0 p0, u = tJ ℓ0 t0 p0 /\ rtc NPar p0 p /\ rtc Par t0 t.
Proof.
  move E : (tJ ℓ0 t p) => T h. move : t p E.
  elim : u T /h; hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Sig_inv u ℓ0 A B :
  rtc NPar u (tSig ℓ0 A B) ->
  exists A0 B0, u = tSig ℓ0 A0 B0 /\ rtc Par A0 A /\ rtc Par B0 B.
Proof.
  move E : (tSig ℓ0 A B) => T h.
  move : A B E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Pack_inv u ℓ0 A B :
  rtc NPar u (tPack ℓ0 A B) ->
  exists A0 B0, u = tPack ℓ0 A0 B0 /\ rtc Par A0 A /\ rtc Par B0 B.
Proof.
  move E : (tPack ℓ0 A B) => T h.
  move : A B E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma LoRed_IsAbs_inv a b :
  rtc LoRed a b ->
  isAbs a -> isAbs b.
Proof. induction 1; hauto inv:LoRed. Qed.

Lemma LoRed_IsPack_inv a b :
  rtc LoRed a b ->
  isPack a -> isPack b.
Proof. induction 1; hauto inv:LoRed. Qed.

Lemma LoRed_IsNum_inv a b :
  rtc LoRed a b ->
  isNum a -> isNum b.
Proof. induction 1; hauto inv:LoRed. Qed.

Lemma LoRed_Abs_inv ℓ a b :
  rtc LoRed (tAbs ℓ a) b ->
  exists a0, b = tAbs ℓ a0 /\ rtc LoRed a a0.
Proof.
  move E : (tAbs ℓ a) => u h.
  move : ℓ a E.
  elim : u b / h.
  - hauto lq:on ctrs:rtc.
  - move => a b c h hb ih ℓ a0 ?. subst.
    inversion h; subst.
    hauto lq:on ctrs:rtc.
Qed.

Lemma NPar_Let_inv u a ℓ0 ℓ1 b :
  rtc NPar u (tLet ℓ0 ℓ1 a b) ->
  exists a0 b0, u = tLet ℓ0 ℓ1 a0 b0 /\ rtc NPar a0 a /\ rtc Par b0 b.
Proof.
  move E : (tLet ℓ0 ℓ1 a b) => T h.
  move : a b E.
  elim : u T /h.
  - hauto lq:on ctrs:rtc inv:NPar.
  - hauto lq:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Refl_inv u :
  rtc NPar u tRefl ->
  u = tRefl.
Proof.
  move E : tRefl => T h.
  move : E.
  elim : u T/h; hauto l:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_TT_inv u :
  rtc NPar u tTT ->
  u = tTT.
Proof.
  move E : tTT => T h.
  move : E.
  elim : u T/h; hauto l:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Zero_inv u :
  rtc NPar u tZero ->
  u = tZero.
Proof.
  move E : tZero => T h.
  move : E.
  elim : u T/h; hauto l:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma NPar_Unit_inv u :
  rtc NPar u tUnit ->
  u = tUnit.
Proof.
  move E : tUnit => T h.
  move : E.
  elim : u T/h; hauto l:on inv:NPar ctrs:Par, rtc.
Qed.

Lemma LoRed_App_Cong a0 a1 ℓ b0 b1 :
  rtc LoRed a0 a1 ->
  ne a1 ->
  rtc LoRed b0 b1 ->
  rtc LoRed (tApp a0 ℓ b0) (tApp a1 ℓ b1).
Proof.
  move => h. move : b0 b1.
  elim : a0 a1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - move => a0 a1 a2 h0 h1 ih b0 b1 ha2 h.
    move : ih h (ha2) => /[apply]/[apply] h.
    apply : rtc_l; eauto.
    apply LoR_App0=>//.
    apply /negP.
    move => ?.
    have : isAbs a2 by hauto q:on ctrs:rtc use:LoRed_IsAbs_inv.
    move : ha2; clear. elim : a2 => //=.
Qed.

Lemma LoRed_Ind_Cong ℓ c0 c1 a0 a1 b0 b1 :
  rtc LoRed c0 c1 ->
  ne c1 ->
  rtc LoRed a0 a1 ->
  nf a1 ->
  rtc LoRed b0 b1 ->
  rtc LoRed (tInd ℓ a0 b0 c0) (tInd ℓ a1 b1 c1).
Proof.
  move => h. move : a0 a1 b0 b1.
  elim : c0 c1 /h.
  - move => c a0 a1 + + h h0.
    elim : a0 a1  /h0; last by hauto lq:on ctrs:rtc,LoRed.
    move => a b0 b1 h0 h1.
    elim : b0 b1 /h1; last by hauto lq:on ctrs:rtc,LoRed.
    eauto using rtc_refl.
  - move => c0 c1 c2 hc hc' ih a0 a1 b0 b1 nec ha nfa hb.
    apply : rtc_l; eauto.
    apply LoR_Ind0; last by eauto using rtc_l.
    apply /negP.
    move => ?.
    have : isNum c2 by hauto q:on ctrs:rtc use:LoRed_IsNum_inv.
    move : nec. clear. elim : c2 => //=.
Qed.

Lemma LoRed_Pi_Cong ℓ A0 A1 B0 B1 :
  rtc LoRed A0 A1 ->
  nf A1 ->
  rtc LoRed B0 B1 ->
  rtc LoRed (tPi ℓ A0 B0) (tPi ℓ A1 B1).
Proof.
  move => h. move : B0 B1.
  elim : A0 A1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - move => a0 a1 a2 h0 h1 ih b0 b1 ha2 h.
    move : ih h (ha2) => /[apply]/[apply] h.
    apply : rtc_l; eauto.
    apply LoR_Pi0=>//.
Qed.

Lemma LoRed_Sig_Cong ℓ A0 A1 B0 B1 :
  rtc LoRed A0 A1 ->
  nf A1 ->
  rtc LoRed B0 B1 ->
  rtc LoRed (tSig ℓ A0 B0) (tSig ℓ A1 B1).
Proof.
  move => h. move : B0 B1.
  elim : A0 A1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - move => a0 a1 a2 h0 h1 ih b0 b1 ha2 h.
    move : ih h (ha2) => /[apply]/[apply] h.
    apply : rtc_l; eauto.
    apply LoR_Sig0=>//.
Qed.

Lemma LoRed_Pack_Cong ℓ A0 A1 B0 B1 :
  rtc LoRed A0 A1 ->
  nf A1 ->
  rtc LoRed B0 B1 ->
  rtc LoRed (tPack ℓ A0 B0) (tPack ℓ A1 B1).
Proof.
  move => h. move : B0 B1.
  elim : A0 A1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - move => a0 a1 a2 h0 h1 ih b0 b1 ha2 h.
    move : ih h (ha2) => /[apply]/[apply] h.
    apply : rtc_l; eauto.
    apply LoR_Pack0=>//.
Qed.

Lemma LoRed_Absurd_Cong a b :
  rtc LoRed a b ->
  rtc LoRed (tAbsurd a) (tAbsurd b).
Proof. induction 1; hauto lq:on ctrs:rtc,LoRed. Qed.

Lemma LoRed_Eq_Cong ℓ a0 a1 b0 b1 :
  rtc LoRed a0 a1 ->
  nf a1 ->
  rtc LoRed b0 b1 ->
  rtc LoRed (tEq ℓ a0 b0) (tEq ℓ a1 b1).
Proof.
  move => h. move : b0 b1.
  elim : a0 a1 /h; last by hauto lq:on ctrs:rtc, LoRed.
  move => ? b0 b1 ? h.
  elim : b0 b1 /h; last by hauto lq:on ctrs:rtc,LoRed.
  eauto using rtc_refl.
Qed.

Lemma LoRed_J_Cong a0 a1 ℓ b0 b1 :
  rtc LoRed a0 a1 ->
  ne a1 ->
  rtc LoRed b0 b1 ->
  rtc LoRed (tJ ℓ b0 a0) (tJ ℓ b1 a1).
Proof.
  move => h. move : b0 b1.
  elim : a0 a1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - hauto lq:on ctrs:rtc, LoRed.
Qed.

Lemma LoRed_Seq_Cong a0 a1 ℓ b0 b1 :
  rtc LoRed a0 a1 ->
  ne a1 ->
  rtc LoRed b0 b1 ->
  rtc LoRed (tSeq ℓ a0 b0) (tSeq ℓ a1 b1).
Proof.
  move => h. move : b0 b1.
  elim : a0 a1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - hauto lq:on ctrs:rtc, LoRed.
Qed.

Lemma LoRed_Let_Cong ℓ0 ℓ1 a0 a1 b0 b1 :
  rtc LoRed a0 a1 ->
  ne a1 ->
  rtc LoRed b0 b1 ->
  rtc LoRed (tLet ℓ0 ℓ1 a0 b0) (tLet ℓ0 ℓ1 a1 b1).
Proof.
  move => h. move : b0 b1.
  elim : a0 a1 /h.
  - move => a b0 b1 h h0.
    elim : b0 b1 /h0; hauto lq:on ctrs:rtc,LoRed.
  - move => a0 a1 a2 h0 h1 ih b0 b1 ha2 h.
    move : ih h (ha2) => /[apply]/[apply] h.
    apply : rtc_l; eauto.
    apply LoR_Let0=>//.
    apply /negP.
    move => ?.
    have : isPack a2 by hauto q:on ctrs:rtc use:LoRed_IsPack_inv.
    move : ha2; clear. elim : a2 => //=.
Qed.

(* Lemma 5.25 (Standardization) *)
Lemma standardization a b :
  rtc Par a b -> nf b ->
  rtc LoRed a b.
Proof.
  elim : b a =>//=.
  - move => n a /factorization.
    hauto lq:on rew:off use:NPar_Var_inv, HReds_LoReds unfold:subrelation.
  - move => ℓ b ihb a /factorization.
    move => [a0][h0].
    move /NPar_Abs_inv => [a1][?]ha1. subst.
    move : ihb ha1; repeat move/[apply].
    move => ?. move/HReds_LoReds in h0.
    apply : rtc_transitive; eauto.
    by apply LoRed_Abs_Cong.
  - move => a iha ℓ b ihb u /factorization.
    move => [u0][hu]hu0 /andP.
    move => [].
    move /NPar_App_inv : hu0.
    move => [a0][b0][?][h0]h1. subst.
    move /[dup] /ne_nf => *.
    have {}iha:rtc LoRed a0 a by sfirstorder use:NPars_Pars.
    have {}ihb:rtc LoRed b0 b by sfirstorder.
    move /HReds_LoReds in hu.
    apply : rtc_transitive; eauto.
    sfirstorder use:LoRed_App_Cong.
  - move => ℓ A ihA B ihB u /factorization.
    move => [u0][hu]hu0 /andP.
    move => [? ?].
    move /NPar_Pi_inv : hu0.
    move => [a0][b0][?][h0]h1. subst.
    qauto l:on use:LoRed_Pi_Cong, rtc_transitive, HReds_LoReds.
  - move => n a /factorization.
    move => [u][hu]hu0 _.
    move /HReds_LoReds in hu.
    move /NPar_Univ_inv in hu0. by subst.
  - move => a /factorization.
    move => [u0][hu]hu0 _.
    move /HReds_LoReds in hu.
    move /NPar_Void_inv in hu0. by subst.
  - move => a iha u /factorization.
    move => [u0][hu]hu0 ?.
    move /NPar_Absurd_inv : hu0 => [u1][hu1]hu2. subst.
    move /HReds_LoReds in hu.
    apply : rtc_transitive; eauto.
    sfirstorder use:LoRed_Absurd_Cong, ne_nf.
  - move => ℓ a iha b ihb u /factorization.
    move => [u0][hu]hu0 ?.
    have ? : nf a /\ nf b by sfirstorder b:on.
    move /HReds_LoReds in hu. apply : rtc_transitive; eauto.
    move /NPar_Eq_inv : hu0 => [a0][b0][?][h0]h1. subst.
    sfirstorder use:LoRed_Eq_Cong, ne_nf.
  - move => ℓ a iha b ihb u /factorization.
    move => [u0][hu]hu0 /andP.
    move => [*].
    move /NPar_J_inv : hu0 => [t0][p0][?][h0]h1. subst.
    move /HReds_LoReds in hu.
    apply : rtc_transitive; eauto.
    sfirstorder use:LoRed_J_Cong, ne_nf, NPars_Pars.
  - move => u /factorization.
    move => [u0][hu0]hu1 _.
    move /NPar_Refl_inv : hu1 => ?. subst.
    eauto using HReds_LoReds.
  - move => ℓ A ihA B ihB u /factorization.
    move => [u0][hu]hu0 /andP.
    move => [? ?].
    move /NPar_Sig_inv : hu0.
    move => [a0][b0][?][h0]h1. subst.
    qauto l:on use:LoRed_Sig_Cong, rtc_transitive, HReds_LoReds.
  - move => ℓ a iha b ihb u /factorization.
    move => [u0][hu0]hu1 /andP.
    move => [? ?].
    move /HReds_LoReds in hu0.
    apply : rtc_transitive; eauto.
    move /NPar_Pack_inv : hu1 => [A0][B0][?][h0]h1. subst.
    sfirstorder use:LoRed_Pack_Cong.
  - move => ℓ ℓ0 a iha b ihb u /factorization.
    move => [u0][/HReds_LoReds hu0].
    move /NPar_Let_inv => [a0][b0][?][h0]h1. subst.
    move /andP => ?.
    apply : rtc_transitive; eauto.
    sfirstorder use:ne_nf, NPars_Pars, LoRed_Let_Cong.
  - move => a /factorization.
    move => [u0][/HReds_LoReds hu0].
    move /NPar_Zero_inv => ?. by subst.
  - move => a iha a0 /factorization.
    move => [u0][/HReds_LoReds hu0].
    move /NPar_Suc_inv.
    hauto lq:on use:rtc_transitive, LoRed_Suc_Cong.
  - move => ℓ a iha b ihb c ihc u /factorization.
    move => [u0][/HReds_LoReds hu0].
    move /NPar_Ind_inv.
    move => [a0][b0][c0][?][hc][ha]hb.
    move /andP => [+ h].
    move /andP => [? ?]. subst.
    apply : rtc_transitive; eauto.
    sfirstorder use:NPars_Pars, ne_nf, LoRed_Ind_Cong.
  - qauto l:on use:factorization, HReds_LoReds, NPar_Nat_inv.
  - qauto l:on use:factorization, HReds_LoReds, NPar_TT_inv.
  - move => ℓ a iha b ihb u /factorization.
    move => [u0][/HReds_LoReds hu0].
    move /NPar_Seq_inv.
    hauto lqb:on use:NPars_Pars, ne_nf, LoRed_Seq_Cong, rtc_transitive.
  - qauto l:on use:factorization, HReds_LoReds, NPar_Unit_inv.
Qed.

Fixpoint LoRedOpt a :=
  match a with
  | tPi ℓ0 A B =>
      match LoRedOpt A with
      | Some A0 => Some (tPi ℓ0 A0 B)
      | None => match LoRedOpt B with
               | Some B0 => Some (tPi ℓ0 A B0)
               | None => None
               end
      end
  | tAbs ℓ0 a =>
      match LoRedOpt a with
      | Some a0 => Some (tAbs ℓ0 a0)
      | None => None
      end
  | tApp a ℓ0 b =>
      match a with
      | tAbs ℓ1 a0 =>
          if T_eqb ℓ0 ℓ1
          then Some a0[b..]
          else None
      | _ => match LoRedOpt a with
            | Some a0 => Some (tApp a0 ℓ0 b)
            | None => match LoRedOpt b with
                     | Some b0 => Some (tApp a ℓ0 b0)
                     | None => None
                     end
            end
      end
  | tAbsurd a =>
      match LoRedOpt a with
      | Some a0 => Some (tAbsurd a0)
      | None => None
      end
  | tEq ℓ0 a b =>
      match LoRedOpt a with
      | Some a0 => Some (tEq ℓ0 a0 b)
      | None => match LoRedOpt b with
               | Some b0 => Some (tEq ℓ0 a b0)
               | None => None
               end
      end
  | tJ ℓp t p =>
      match p with
      | tRefl => Some t
      | _ =>
          match LoRedOpt p with
          | Some p0 => Some (tJ ℓp t p0)
          | None => match LoRedOpt t with
                   | Some t0 => Some (tJ ℓp t0 p)
                   | None => None
                   end
          end
      end
  | tSig ℓ0 A B =>
      match LoRedOpt A with
      | Some A0 => Some (tSig ℓ0 A0 B)
      | None => match LoRedOpt B with
               | Some B0 => Some (tSig ℓ0 A B0)
               | None => None
               end
      end

  | tPack ℓ0 A B =>
      match LoRedOpt A with
      | Some A0 => Some (tPack ℓ0 A0 B)
      | None => match LoRedOpt B with
               | Some B0 => Some (tPack ℓ0 A B0)
               | None => None
               end
      end


  | tLet ℓ0 ℓ1 (tPack ℓ2 a b) c =>
      if T_eqb ℓ0 ℓ2
      then Some c[b .: a..]
      else None
  | tLet ℓ0 ℓ1 a b => match LoRedOpt a with
                     | Some a0 => Some (tLet ℓ0 ℓ1 a0 b)
                     | None => match LoRedOpt b with
                              | Some b0 => Some (tLet ℓ0 ℓ1 a b0)
                              | None => None
                              end
                     end
  | var_tm _ => None
  | tUniv _ => None
  | tRefl => None
  | tVoid => None
  | tNat => None
  | tZero => None
  | tSuc a => match LoRedOpt a with
             | Some a0 => Some (tSuc a0)
             | None => None
             end
  | tInd ℓ a b tZero => Some a
  | tInd ℓ a b (tSuc c) =>
      Some (b[(tInd ℓ a b c) .: c ..])
  | tInd ℓ a b c =>
      match LoRedOpt c with
      | Some c0 => Some (tInd ℓ a b c0)
      | None => match LoRedOpt a with
               | Some a0 => Some (tInd ℓ a0 b c)
               | None => match LoRedOpt b with
                        | Some b0 => Some (tInd ℓ a b0 c)
                        | None =>None
                        end
               end
      end
  | tSeq _ tTT b => Some b
  | tSeq ℓ a b =>
      match LoRedOpt a with
      | Some a0 => Some (tSeq ℓ a0 b)
      | None => match LoRedOpt b with
               | Some b0 =>  Some (tSeq ℓ a b0)
               | None => None
               end
      end
  | tUnit => None
  | tTT => None
  end.

Lemma nf_no_red a : nf a -> LoRedOpt a = None.
Proof.
  elim : a=> //=; hauto q:on use:ne_nf b:on inv:tm.
Qed.

Lemma LoRed_LoRedOpt a b : LoRed a b -> LoRedOpt a = Some b.
Proof.
  move => h. elim : a b /h => //=.
  - hauto lq:on.
  - hauto lq:on use:nf_no_red.
  - hauto lq:on rew:off use:nf_no_red.
  - move => > ? ? iha /=.
    rewrite {}iha.
    hauto lq:on b:on.
  - move => a ℓ0 b0 b1 nea hb ihb /=.
    rewrite ihb.
    have -> : LoRedOpt a = None by hauto lq:on use:nf_no_red, ne_nf.
    hauto q:on inv:tm.
  - move => a b ℓ.
    case : T_eqdec => //.
  - hauto lq:on.
  - hauto lq:on.
  - hauto lq:on use:nf_no_red.
  - hauto q:on inv: LoRed lq:on rew:off.
  - move => ℓp t0 t1 p hp ha iha.
    rewrite !{}iha.
    hauto b:on use:nf_no_red, ne_nf.
  - hauto lq:on.
  - hauto lq:on use:nf_no_red.
  - hauto lq:on.
  - hauto lq:on use:nf_no_red.
  - move => ℓ0 ℓ1 a0 a1 b hp ha iha.
    rewrite !{}iha.
    hauto q:on inv:LoRed.
  - move => ℓ0 ℓ1 a b0 b1 nea hb ihb.
    rewrite !{}ihb.
    hauto b:on drew:off inv:tm use:nf_no_red, ne_nf.
  - move => ℓ0 ℓ1 a b c.
    case : T_eqdec => //.
  - move => ℓ a b c0 c1 nc hc ihc.
    rewrite !{}ihc.
    hauto q:on inv:LoRed.
  - move => ℓ a0 a1 b c nec ha iha.
    rewrite !{}iha.
    hauto b:on drew:off inv:tm use:nf_no_red, ne_nf.
  - move => ℓ a b0 b1 c nec nfa hb ihb.
    rewrite !{}ihb.
    set q := (X in X = _).
    have -> : q = match LoRedOpt c with
           | Some c0 => Some (tInd ℓ a b0 c0)
           | None => match LoRedOpt a with
                     | Some a0 => Some (tInd ℓ a0 b0 c)
                     | None => Some (tInd ℓ a b1 c)
                     end
                  end by hauto dep:on inv:tm.
    move {q}.
    hauto b:on drew:off inv:tm use:nf_no_red, ne_nf.
  - hauto lq:on.
  - move => ℓ a0 a1 b h  /[dup] ? ->.
    have : a0 <> tTT by hauto lq:on. clear.
    case : a0 => //=.
  - move => ℓ a b0 b1 ha hb /[dup] h ->.
    move E : (LoRedOpt a) => T.
    have : a <> tTT by hauto lq:on.
    case : T a ha E => //=.
    hauto l:on use:nf_no_red, ne_nf.
    hauto lq:on rew:off.
Qed.

Definition LoRed' a b := LoRedOpt a = Some b.

Lemma LoRed_LoRed' : subrelation LoRed LoRed'.
Proof. sfirstorder use:LoRed_LoRedOpt unfold:subrelation, LoRed'. Qed.

Lemma LoReds_LoReds' a b : rtc LoRed a b -> rtc LoRed' a b.
Proof. sfirstorder use:LoRed_LoRed', relations.rtc_subrel unfold:LoRed', subrelation. Qed.

Lemma standardization' a b :
  rtc Par a b -> nf b ->
  rtc LoRed' a b.
Proof.
  sfirstorder use:LoReds_LoReds', standardization.
Qed.

Polymorphic Inductive IsAbs {A : Type} (a : tm) (b1 : A) (F : T -> tm -> A) : A -> tm -> Prop :=
| IsAbsTrue a0 ℓ :  IsAbs a b1 F (F ℓ a0) (tAbs ℓ a0)
| isAbsFalse  : IsAbs a b1 F b1 a.

Polymorphic Lemma IsAbsP {A : Type} a (b1 : A) F :
  let e := match a with
           | tAbs ℓ a => F ℓ a
           | _ => b1
           end in
  IsAbs a b1 F e a.
Proof. hauto lq:on ctrs:IsAbs inv:tm. Qed.

Polymorphic Inductive IsPack {A : Type} (a : tm) (b1 : A) (F : T -> tm -> tm -> A) : A -> tm -> Prop :=
| IsPackTrue a0 a1 ℓ :  IsPack a b1 F (F ℓ a0 a1) (tPack ℓ a0 a1)
| isPackFalse  : IsPack a b1 F b1 a.

Polymorphic Lemma IsPackP {A : Type} a (b1 : A) F :
  let e := match a with
           | tPack ℓ a0 a1 => F ℓ a0 a1
           | _ => b1
           end in
  IsPack a b1 F e a.
Proof. hauto lq:on ctrs:IsPack inv:tm. Qed.

Polymorphic Inductive IsNum {A : Type} (a : tm) (b1 : A) (F : tm -> A) (b2 : A) : A -> tm -> Prop :=
| IsZero :  IsNum a b1 F b2 b1 tZero
| IsSuc a0  : IsNum a b1 F b2 (F a0) (tSuc a0)
| IsNumFalse : IsNum a b1 F b2 b2 a.

Polymorphic Lemma IsNumP {A : Type} a (b1 : A) F b2  :
  IsNum a b1 F b2 (match a with
                   | tZero => b1
                   | tSuc a0 => F a0
                   | _ => b2
                   end) a.
Proof. hauto lq:on ctrs:IsNum inv:tm. Qed.

Lemma LoRedOpt_Par a b :
  LoRedOpt a = Some b -> a ⇒ b.
Proof.
  elim : a b => //=.
  - hauto q:on ctrs:Par.
  - move => a iha ℓ b ihb u.
    case : IsAbsP.
    + move => a0 ℓ0.
      case : T_eqdec => // ?. subst.
      move => [?]. subst.
      hauto lq:on ctrs:Par use:Par_refl.
    + move E0 : (LoRedOpt a) => n.
      case : n E0 => //=.
      * move => a0 ? h.
        have {}h : u = tApp a0 ℓ b by destruct a; hauto  b:on drew:off. subst.
        hauto lq:on ctrs:Par use:Par_refl.
      * move E1 : (LoRedOpt b) => t.
        case : t E1 => //=.
        destruct a; hauto qb:on drew:off ctrs:Par use:Par_refl.
  - hauto lq:on rew:off inv:tm ctrs:Par use:Par_refl.
  - hauto lq:on rew:off inv:tm ctrs:Par use:Par_refl.
  - hauto lq:on rew:off inv:tm ctrs:Par use:Par_refl.
  - hauto q:on dep:on ctrs:Par inv:tm use:Par_refl.
  - hauto lq:on rew:off inv:tm ctrs:Par use:Par_refl.
  - hauto lq:on rew:off inv:tm ctrs:Par use:Par_refl.
  - move => ℓ0 ℓ1 a iha b ihb u.
    case : IsPackP.
    + move => a0 a1 ℓ.
      case : T_eqdec => // ?. subst.
      hauto lq:on use:Par_refl ctrs:Par.
    + move E0 : (LoRedOpt a) => T.
      case : T E0=> //=.
      * move => a0 ? h.
        have {}h :u = tLet ℓ0 ℓ1 a0 b by destruct a; hauto b:on drew:off. subst.
        hauto lq:on ctrs:Par use:Par_refl.
      * move E0 : (LoRedOpt b) => T.
        elim : T E0=>//=; destruct a;
                 hauto qb:on drew:off ctrs:Par use:Par_refl.
  - hauto q:on ctrs:Par.
  - move => ℓ a iha b ihb c ihc b0.
    case : IsNumP => //=.
    + hauto q:on ctrs:Par use:Par_refl.
    + move => a0 [?]. subst.
      hauto lq:on ctrs:Par use:Par_refl.
    + move E0 : (LoRedOpt c) => T.
      case : T E0 => //=.
      * hauto lq:on ctrs:Par use:Par_refl.
      * move E0 : (LoRedOpt a) => T.
        case : T E0 => //=.
        ** move => a0 ? h.
           hauto lq:on rew:off inv:tm ctrs:Par use:Par_refl.
        ** move E0 : (LoRedOpt b) => T.
           case : T E0 => //=.
           hauto lq:on rew:off inv:tm ctrs:Par use:Par_refl.
  - hauto q:on dep:on ctrs:Par inv:tm use:Par_refl.
Qed.

Lemma LoRed'_Par a b :
  LoRed' a b -> a ⇒ b.
Proof. hauto lq:on use:LoRedOpt_Par unfold:LoRed'. Qed.

Lemma LoReds'_Pars a b :
  rtc LoRed' a b -> a ⇒* b.
Proof.
  hauto l:on use:relations.rtc_subrel, LoRed'_Par unfold:subrelation.
Qed.

Lemma nf_no_lored a : nf a -> LoRedOpt a = None.
Proof.
  rewrite /LoRed'.
  elim : a => //=; hauto  inv:tm b:on drew:off.
Qed.

Lemma LoRed_wn_sn a b :
  rtc LoRed' a b -> nf b ->
  relations.sn LoRed' a.
Proof.
  rewrite /LoRed'.
  induction 1.
  - hauto q:on ctrs:Acc use:nf_no_lored.
  - hauto l:on ctrs:Acc.
Qed.

Lemma LoRed'_nf_unique a b c :
  rtc LoRed' a b ->
  rtc LoRed' a c ->
  LoRedOpt b = None ->
  LoRedOpt c = None ->
  b = c.
Proof.
  induction 1; hauto l:on inv:rtc unfold:LoRed'.
Qed.

(* Corollary 5.26 (Normalization is decidable) *)
Definition LoRed_normalize a (h : wn a) : {x : tm | nf x /\ rtc Par a x}.
Proof.
  unfold wn in h.
  have {}h : relations.sn LoRed' a /\ exists b, rtc LoRed' a b /\ nf b /\ rtc Par a b by hauto lq:on use:LoRed_wn_sn, standardization'.
  move : h => [h0 h1].
  induction h0 as [a h ih]. simpl in *. rewrite {1}/LoRed' in ih.
  destruct (LoRedOpt a) as [a0 |] eqn:eq .
  - specialize ih with (1 := eq_refl).
    have {}eq : LoRed' a a0 by sfirstorder unfold:LoRed'.
    destruct ih.
    + move : h1 => [b][hb0][hb1]hb2.
      exists b. move => [:tr0].
      repeat split => //.
      abstract : tr0.
      destruct hb0.
      hauto q:on use:nf_no_lored unfold:LoRed'.
      scongruence unfold:LoRed'.
      hauto l:on use:LoReds'_Pars.
    + exists x.
      split; first by tauto.
      hauto lq:on ctrs:rtc use:LoRed'_Par unfold:LoRed'.
  - exists a.
    case : h1 => [b [h10 [h11 h12]]].
    suff : a = b by hauto lq:on.
    hauto lq:on use:LoRed'_nf_unique, nf_no_lored.
Defined.

End factorization_sig.
