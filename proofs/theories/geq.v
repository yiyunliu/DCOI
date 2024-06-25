Require Import imports.

Module Type geq_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice).

  Definition econtext := list T.
  Open Scope lattice_scope.

  Definition elookup i Ξ (ℓ : T) := nth_error Ξ i = Some ℓ.

  Inductive IOk (Ξ : econtext) (ℓ : T) : tm -> Prop :=
  | IO_Var i ℓ0 :
    elookup i Ξ ℓ0 ->
    ℓ0 ⊆ ℓ ->
    (* ------- *)
    IOk Ξ ℓ (var_tm i)
  | IO_Univ i :
    (* -------- *)
    IOk Ξ ℓ (tUniv i)
  | IO_Pi ℓ0 A B :
    IOk Ξ ℓ A ->
    IOk (ℓ0 :: Ξ) ℓ B ->
    (* --------------------- *)
    IOk Ξ ℓ (tPi ℓ0 A B)
  | IO_Abs ℓ0 a :
    IOk (ℓ0 :: Ξ) ℓ a ->
    (* -------------------- *)
    IOk Ξ ℓ (tAbs ℓ0 a)
  | IO_App a ℓ0 b :
    IOk Ξ ℓ a ->
    IOk Ξ ℓ0 b ->
    (* ------------------------- *)
    IOk Ξ ℓ (tApp a ℓ0 b)
  | IO_Void :
    IOk Ξ ℓ tVoid
  | IO_Absurd a:
    IOk Ξ ℓ (tAbsurd a)
  | IO_Refl :
    IOk Ξ ℓ tRefl
  | IO_Eq ℓ0 a b A :
    ℓ0 ⊆ ℓ ->
    IOk Ξ ℓ0 a ->
    IOk Ξ ℓ0 b ->
    (* -------------- *)
    IOk Ξ ℓ (tEq ℓ0 a b A)
  | IO_J ℓp t p :
    ℓp ⊆ ℓ ->
    IOk Ξ ℓ t ->
    IOk Ξ ℓp p ->
    (* --------------- *)
    IOk Ξ ℓ (tJ ℓp t p)

  | IO_Sig ℓ0 A B :
    IOk Ξ ℓ A ->
    IOk (ℓ0 :: Ξ) ℓ B ->
    (* --------------- *)
    IOk Ξ ℓ (tSig ℓ0 A B)

  | IO_Pack ℓ0 a b :
    IOk Ξ ℓ0 a ->
    IOk Ξ ℓ b ->
    (* --------------- *)
    IOk Ξ ℓ (tPack ℓ0 a b)

  | IO_Let ℓ0 ℓ1 a b :
    ℓ1 ⊆ ℓ ->
    IOk Ξ ℓ1 a ->
    IOk (ℓ1::ℓ0::Ξ) ℓ b ->
    (* -------------------- *)
    IOk Ξ ℓ (tLet ℓ0 ℓ1 a b)
  | IO_D :
    (*  *)
    IOk Ξ ℓ tD
  | IO_Down ℓ0 p :
    IOk Ξ ℓ p ->
    IOk Ξ ℓ (tDown ℓ0 p).

  Inductive IEq (Ξ : econtext) (ℓ : T) : tm -> tm -> Prop :=
  | I_Var i ℓ0 :
    elookup i Ξ ℓ0 ->
    ℓ0 ⊆ ℓ ->
    (* ------- *)
    IEq Ξ ℓ (var_tm i) (var_tm i)
  | I_Univ i :
    (* -------- *)
    IEq Ξ ℓ (tUniv i) (tUniv i)
  | I_Pi ℓ0 A0 A1 B0 B1 :
    IEq Ξ ℓ A0 A1 ->
    IEq (ℓ0 :: Ξ) ℓ B0 B1 ->
    (* --------------------- *)
    IEq Ξ ℓ (tPi ℓ0 A0 B0) (tPi ℓ0 A1 B1)
  | I_Abs ℓ0 a0 a1 :
    IEq (ℓ0 :: Ξ) ℓ a0 a1 ->
    (* -------------------- *)
    IEq Ξ ℓ (tAbs ℓ0 a0) (tAbs ℓ0 a1)
  | I_App a0 a1 ℓ0 b0 b1 :
    IEq Ξ ℓ a0 a1 ->
    GIEq Ξ ℓ ℓ0 b0 b1 ->
    (* ------------------------- *)
    IEq Ξ ℓ (tApp a0 ℓ0 b0) (tApp a1 ℓ0 b1)
  | I_Void :
    IEq Ξ ℓ tVoid tVoid
  | I_Absurd a b :
    IEq Ξ ℓ (tAbsurd a) (tAbsurd b)
  | I_Refl :
    IEq Ξ ℓ tRefl tRefl
  | I_Eq ℓ0 a0 a1 b0 b1 A0 A1 :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ a0 a1 ->
    IEq Ξ ℓ b0 b1 ->
    (* -------------- *)
    IEq Ξ ℓ (tEq ℓ0 a0 b0 A0) (tEq ℓ0 a1 b1 A1)
  | I_J ℓp t0 t1 p0 p1 :
    ℓp ⊆ ℓ ->
    IEq Ξ ℓ t0 t1 ->
    IEq Ξ ℓ p0 p1 ->
    (* --------------- *)
    IEq Ξ ℓ (tJ ℓp t0 p0) (tJ ℓp t1 p1)
  | I_Sig ℓ0 A0 B0 A1 B1 :
    IEq Ξ ℓ A0 A1 ->
    IEq (ℓ0 :: Ξ) ℓ B0 B1 ->
    (* --------------- *)
    IEq Ξ ℓ (tSig ℓ0 A0 B0) (tSig ℓ0 A1 B1)

  | I_Pack ℓ0 a0 b0 a1 b1 :
    GIEq Ξ ℓ ℓ0 a0 a1 ->
    IEq Ξ ℓ b0 b1 ->
    (* --------------- *)
    IEq Ξ ℓ (tPack ℓ0 a0 b0) (tPack ℓ0 a1 b1)

  | I_Let ℓ0 ℓ1 a0 b0 a1 b1 :
    IEq Ξ ℓ a0 a1 ->
    IEq (ℓ1::ℓ0::Ξ) ℓ b0 b1 ->
    (* -------------------- *)
    IEq Ξ ℓ (tLet ℓ0 ℓ1 a0 b0) (tLet ℓ0 ℓ1 a1 b1)

  | I_D :
    (*  *)
    IEq Ξ ℓ tD tD

  | I_Down ℓ0 p0 p1 :
    IEq Ξ ℓ p0 p1 ->
    IEq Ξ ℓ (tDown ℓ0 p0) (tDown ℓ0 p1)

  with GIEq (Ξ : econtext) (ℓ : T) : T -> tm -> tm -> Prop :=
  | GI_Dist ℓ0 A B :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ A B ->
    (* -------------- *)
    GIEq Ξ ℓ ℓ0 A B
  | GI_InDist ℓ0 A B :
    ~ (ℓ0 ⊆ ℓ) ->
    (* -------------- *)
    GIEq Ξ ℓ ℓ0 A B.

  Fixpoint compute_level (Ξ : econtext) a : option T :=
    match a with
    | var_tm i => nth_error Ξ i
    | tApp a ℓ0 b => compute_level Ξ a
    | tAbs ℓ0 a => compute_level (ℓ0 :: Ξ) a
    | tJ ℓp t p => match compute_level Ξ t with
                  | Some ℓ => Some (ℓ ∪ ℓp)
                  | None => Some ℓp
                  end
    | tEq ℓ0 a b A => match compute_level Ξ a with
                  | Some ℓa =>
                      match compute_level Ξ b with
                      | Some ℓb => Some (ℓa ∪ ℓb)
                      | None => Some ℓa
                      end
                  | None => compute_level Ξ b
                  end
    | tRefl => None
    | tVoid => None
    | tD => None
    | tUniv _ => None
    | tAbsurd _ => None
    | tPi ℓ0 A B =>
        match compute_level Ξ A with
        | Some ℓA => match compute_level (ℓ0::Ξ) B with
                    | Some ℓB => Some (ℓA ∪ ℓB)
                    | None => Some ℓA
                    end
        | None => compute_level (ℓ0::Ξ) B
        end
    | tSig ℓ0 A B =>
        match compute_level Ξ A with
        | Some ℓA => match compute_level (ℓ0::Ξ) B with
                    | Some ℓB => Some (ℓA ∪ ℓB)
                    | None => Some ℓA
                    end
        | None => compute_level (ℓ0::Ξ) B
        end

    | tPack ℓ0 A B =>
        match compute_level Ξ A with
        | Some ℓA => match compute_level (ℓ0::Ξ) B with
                    | Some ℓB => Some (ℓA ∪ ℓB)
                    | None => Some ℓA
                    end
        | None => compute_level (ℓ0::Ξ) B
        end

    | tDown ℓ0 a => compute_level Ξ a
    | tLet ℓ0 ℓ1 a b => match compute_level (ℓ1::ℓ0::Ξ) b with
                       | Some ℓb => Some (ℓb ∪ ℓ1)
                       | None => Some ℓ1
                       end
    end.

  #[export]Hint Constructors IOk IEq GIEq : ieq.

  Scheme IEq_ind' := Induction for IEq Sort Prop
      with GIEq_ind' := Induction for GIEq Sort Prop.

  Combined Scheme IEq_mutual from IEq_ind', GIEq_ind'.

  Derive Inversion IOk_inv with (forall Ξ ℓ a, IOk Ξ ℓ a).
  Derive Inversion IEq_inv with (forall Ξ ℓ a b, IEq Ξ ℓ a b).
  Derive Inversion GIEq_inv with (forall Ξ ℓ ℓ0 a b, GIEq Ξ ℓ ℓ0 a b).

  Definition iok_ren_ok ρ Ξ Δ := forall i ℓ, elookup i Ξ ℓ -> exists ℓ0, elookup (ρ i) Δ ℓ0 /\ ℓ0 ⊆ ℓ.

  Definition iok_subst_ok ρ Ξ Δ := forall i ℓ, elookup i Ξ ℓ -> IOk Δ ℓ (ρ i).

End geq_sig.


Module geq_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import geq : geq_sig lattice syntax).

  Module lprop :=  Lattice.All.Properties lattice.
  Import lprop.
  Module solver  :=  Solver lattice.
  Import solver.

  Lemma iok_subsumption Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall ℓ0, ℓ ⊆ ℓ0 -> IOk Ξ ℓ0 a.
  Proof.
    elim : Ξ ℓ a / h; hauto lq:on ctrs:IOk use:leq_trans.
  Qed.

  Lemma iok_subst_id Ξ : iok_subst_ok ids Ξ Ξ.
  Proof.
    hauto lq:on ctrs:IOk unfold:iok_subst_ok solve+:solve_lattice.
  Qed.

  Lemma iok_subst_cons ρ Ξ Δ ℓ a (h : iok_subst_ok ρ Ξ Δ) (ha : IOk Δ ℓ a) :
    iok_subst_ok (a .: ρ) (ℓ :: Ξ) Δ.
  Proof.
    rewrite /iok_subst_ok /elookup.
    case => //= ?.
    case => //= <- //.
  Qed.

  Lemma iok_ren_ok_suc ρ Ξ Δ (h : iok_ren_ok ρ Ξ Δ) :
    forall ℓ0, iok_ren_ok (upRen_tm_tm ρ) (ℓ0 :: Ξ) (ℓ0 :: Δ).
  Proof.
    move => ℓ0.
    rewrite /iok_ren_ok /elookup.
    case=>//=.
    hauto lq:on solve+:solve_lattice.
  Qed.

  Lemma iok_renaming Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall Δ ρ, iok_ren_ok ρ Ξ Δ  ->
           IOk Δ ℓ a⟨ρ⟩.
  Proof.
    elim : Ξ ℓ a / h;
      qauto l:on ctrs:IOk use:IO_Let use:iok_ren_ok_suc, iok_subsumption unfold:elookup, iok_ren_ok.
  Qed.

  Lemma iok_subst_ok_suc ρ Ξ Δ (h : iok_subst_ok ρ Ξ Δ) :
    forall ℓ0, iok_subst_ok (up_tm_tm ρ) (ℓ0 :: Ξ) (ℓ0 :: Δ).
  Proof.
    move => ℓ0.
    rewrite /iok_subst_ok.
    case=>//=.
    - move => _ [<-].
      apply : IO_Var.
      rewrite /elookup //=.
      by rewrite meet_idempotent.
    - move => n ℓ ?.
      asimpl. apply : iok_renaming; eauto.
      hauto lq:on rew:off unfold:iok_ren_ok solve+:solve_lattice.
  Qed.

  Lemma iok_morphing Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall Δ ρ, iok_subst_ok ρ Ξ Δ  ->
           IOk Δ ℓ a[ρ].
  Proof.
    elim : Ξ ℓ a / h; qauto l:on ctrs:IOk use:iok_subst_ok_suc, iok_subsumption unfold:iok_subst_ok, elookup.
  Qed.

  Lemma iok_subst Ξ ℓ ℓ0 a b (h : IOk Ξ ℓ0 a)
    (h0 : IOk (ℓ0::Ξ) ℓ b) : IOk Ξ ℓ b[a..].
  Proof. sfirstorder use:iok_morphing, iok_subst_cons, iok_subst_id. Qed.

  Lemma iok_ieq Ξ ℓ a (h : IOk Ξ ℓ a) :
    forall ℓ0, ℓ ⊆ ℓ0 -> IEq Ξ ℓ0 a a.
  Proof.
    elim : Ξ ℓ a / h; eauto using leq_trans with ieq.
    (* App *)
    - move => Ξ ℓ a ℓ0 b ha iha hb ihb ℓ1 ?.
      apply I_App; eauto.
      case : (sub_eqdec ℓ0 ℓ1) => //; hauto l:on ctrs:GIEq.
    - move => Ξ ℓ ℓ0 a b A hℓ ha iha hb ihb ℓ1 hℓ'.
      have : ℓ0 ⊆ ℓ1 by eauto using leq_trans.
      hauto lq:on ctrs:IEq.
    - hauto lq:on drew:off ctrs:IEq solve+:solve_lattice.
    - move => Ξ ℓ ℓ0 a b ha iha hb ihb ℓ1 ?.
      apply I_Pack; eauto.
      case : (sub_eqdec ℓ0 ℓ1) => //; hauto l:on ctrs:GIEq.
  Qed.

  Lemma elookup_deterministic : forall Ξ i ℓ0 ℓ1,
      elookup i Ξ ℓ0 ->
      elookup i Ξ ℓ1 ->
      ℓ0 = ℓ1.
  Proof. rewrite/elookup =>//. congruence. Qed.

  Lemma ieq_downgrade_mutual : forall Ξ ℓ,
      (forall a b, IEq Ξ ℓ a b ->
              forall ℓ0 c , IEq Ξ ℓ0 a c ->
                       IEq Ξ (ℓ ∩ ℓ0) a b) /\
        (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
                   forall ℓ1 c, GIEq Ξ ℓ1 ℓ0 a c ->
                           GIEq Ξ (ℓ ∩ ℓ1) ℓ0 a b).
  Proof.
    apply IEq_mutual; try qauto l:on inv:IEq,GIEq ctrs:IEq,GIEq.
    - move => Ξ ℓ i ℓ0 hi hℓ ℓ1 c h.
      inversion h; subst.
      apply : I_Var; eauto.
      have ? : ℓ0 = ℓ2 by eauto using elookup_deterministic. subst.
      solve_lattice.
    - hauto lq:on rew:off inv:IEq ctrs:IEq solve+:solve_lattice.
    - hauto lq:on rew:off inv:IEq ctrs:IEq solve+:solve_lattice.
    - hauto q:on inv:GIEq ctrs:GIEq solve+:solve_lattice.
    - hauto lq:on use:GI_InDist solve+:(solve_lattice).
  Qed.

  Lemma ieq_downgrade_leq : forall Ξ ℓ ℓ0 a b c,
      ℓ0 ⊆ ℓ ->
      (IEq Ξ ℓ a b -> IEq Ξ ℓ0 a c -> IEq Ξ ℓ0 a b).
  Proof.
    hauto l:on drew:off use:ieq_downgrade_mutual, meet_commutative.
  Qed.

  Lemma ieq_gieq Ξ ℓ ℓ0 a b (h : forall ℓ0, ℓ ⊆ ℓ0 -> IEq Ξ ℓ0 a b) :
    GIEq Ξ ℓ0 ℓ a b.
  Proof.
    case : (sub_eqdec ℓ ℓ0).
    - firstorder using GI_Dist.
    - move /GI_InDist. apply.
  Qed.

  Lemma iok_gieq Ξ ℓ ℓ0 a (h : IOk Ξ ℓ a) :
    GIEq Ξ ℓ0 ℓ a a.
  Proof. sfirstorder use:iok_ieq, ieq_gieq. Qed.

  Lemma ieq_sym_mutual : forall Ξ ℓ,
      (forall A B, IEq Ξ ℓ A B -> IEq Ξ ℓ B A) /\
        (forall ℓ0 A B, GIEq Ξ ℓ ℓ0 A B -> GIEq Ξ ℓ ℓ0 B A).
  Proof.
    apply IEq_mutual; eauto with ieq.
  Qed.

  Lemma ieq_sym : forall Ξ ℓ,
      (forall A B, IEq Ξ ℓ A B -> IEq Ξ ℓ B A).
  Proof. sfirstorder use:ieq_sym_mutual. Qed.

  Lemma ieq_trans_mutual : forall Ξ ℓ,
      (forall A B, IEq Ξ ℓ A B -> forall C, IEq Ξ ℓ B C -> IEq Ξ ℓ A C) /\
        (forall ℓ0 A B, GIEq Ξ ℓ ℓ0 A B -> forall C, GIEq Ξ ℓ ℓ0 B C -> GIEq Ξ ℓ ℓ0 A C).
  Proof.
    apply IEq_mutual; hauto lq:on ctrs:IEq, GIEq inv:IEq,GIEq.
  Qed.

  Lemma ieq_trans : forall Ξ ℓ A B C, IEq Ξ ℓ A B -> IEq Ξ ℓ B C -> IEq Ξ ℓ A C.
  Proof. sfirstorder use:ieq_trans_mutual. Qed.

  Lemma ieq_pi_inj Ξ ℓ ℓ0 A B A0 B0 :
    IEq Ξ ℓ (tPi ℓ0 A B) (tPi ℓ0 A0 B0) ->
    IEq Ξ ℓ A A0 /\ IEq (ℓ0 :: Ξ) ℓ B B0.
  Proof. qauto l:on inv:IEq. Qed.

  Definition ieq_weakening_helper : forall ℓ ξ (Ξ Δ : econtext),
      iok_ren_ok ξ Ξ Δ ->
      iok_ren_ok (upRen_tm_tm ξ) (ℓ :: Ξ) (ℓ :: Δ).
  Proof.
    move => ℓ0 ξ Ξ Δ h.
    rewrite /iok_ren_ok.
    case => //.
    move => ℓ. rewrite /elookup/= => [->].
    hauto lq:on inv:option solve+:solve_lattice .
  Qed.

  Lemma ieq_weakening_mutual : forall Ξ ℓ,
      (forall a b, IEq Ξ ℓ a b ->
              forall ξ Δ, iok_ren_ok ξ Ξ Δ ->
                     IEq Δ ℓ (ren_tm ξ a) (ren_tm ξ b)) /\
        (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
                   forall ξ Δ, iok_ren_ok ξ Ξ Δ ->
                          GIEq Δ ℓ ℓ0 (ren_tm ξ a) (ren_tm ξ b)).
  Proof.
    apply IEq_mutual; try qauto l: on ctrs:IEq,GIEq use:ieq_weakening_helper unfold:iok_ren_ok solve+:solve_lattice.
    hauto use:I_Var, leq_trans unfold:iok_ren_ok.
  Qed.

Definition ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ :=
  forall i ℓ0, elookup i Ξ ℓ0 -> GIEq Δ ℓ ℓ0 (ξ0 i ) (ξ1 i).

Lemma gieq_refl n Ξ ℓ ℓ0 :
  elookup n Ξ ℓ0 ->
  GIEq Ξ ℓ ℓ0 (var_tm n) (var_tm n).
Proof.
  case : (sub_eqdec ℓ0 ℓ); hauto lq:on ctrs:IEq, GIEq.
Qed.

Lemma ieq_subst_id ℓ Ξ : ieq_good_morphing ℓ ids ids Ξ Ξ.
Proof.
  move => *.
  hauto lq:on ctrs:IEq use:ieq_gieq.
Qed.

Lemma ieq_subst_cons ℓ ℓ0 ξ0 ξ1 Ξ Δ a0 a1
  (h : ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ)
  (ha : GIEq Δ ℓ ℓ0 a0 a1) :
  ieq_good_morphing ℓ (a0 .: ξ0) (a1 .: ξ1) (ℓ0 :: Ξ) Δ.
Proof.
  rewrite /ieq_good_morphing /elookup.
  case => //= ?.
  case => //= <- //.
Qed.

Lemma ieq_morphing_helper ℓ ℓ0 ξ0 ξ1 Ξ Δ :
  ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
  ieq_good_morphing ℓ (up_tm_tm ξ0) (up_tm_tm ξ1) (ℓ0 :: Ξ) (ℓ0 :: Δ).
Proof.
  rewrite /ieq_good_morphing => h.
  case => [|i] ℓ1 //=.
  - sfirstorder use:gieq_refl.
  - asimpl.
    hauto lq:on rew:off use:ieq_weakening_mutual unfold:iok_ren_ok solve+:solve_lattice.
Qed.

Lemma ieq_morphing_helper2 ℓ ℓ0 ℓ1 ξ0 ξ1 Ξ Δ :
  ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
  ieq_good_morphing ℓ (up_tm_tm (up_tm_tm ξ0)) (up_tm_tm (up_tm_tm ξ1)) (ℓ1 :: (ℓ0 :: Ξ)) (ℓ1 :: (ℓ0 :: Δ)).
Proof. hauto lq:on use:ieq_morphing_helper. Qed.

Lemma ieq_morphing_mutual : forall Ξ ℓ,
    (forall a b, IEq Ξ ℓ a b ->
            forall ξ0 ξ1 Δ, ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
            IEq Δ ℓ (subst_tm ξ0 a) (subst_tm ξ1 b)) /\
    (forall ℓ0 a b, GIEq Ξ ℓ ℓ0 a b ->
            forall ξ0 ξ1 Δ, ieq_good_morphing ℓ ξ0 ξ1 Ξ Δ ->
            GIEq Δ ℓ ℓ0 (subst_tm ξ0 a) (subst_tm ξ1 b)).
Proof.
  apply IEq_mutual; try qauto ctrs:IEq,GIEq.
  - hauto lq: on inv: GIEq lqb:on unfold:ieq_good_morphing.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper.
  - hauto lq:on ctrs:IEq use:ieq_morphing_helper2.
  - hauto lq:on ctrs:GIEq unfold:ieq_good_morphing.
Qed.

Lemma ieq_morphing_iok Ξ Δ ℓ a b (h : IEq Ξ ℓ a b) ρ
  (hρ : forall i ℓ0, elookup i Ξ ℓ0 -> IOk Δ ℓ0 (ρ i)) :
  IEq Δ ℓ a[ρ] b[ρ].
Proof.
  sfirstorder use:ieq_morphing_mutual, iok_gieq unfold:ieq_good_morphing.
Qed.

Lemma gieq_morphing_iok Ξ Δ ℓ ℓ0 a b (h : GIEq Ξ ℓ ℓ0 a b) ρ
  (hρ : forall i ℓ0, elookup i Ξ ℓ0 -> IOk Δ ℓ0 (ρ i)) :
  GIEq Δ ℓ ℓ0 a[ρ] b[ρ].
Proof.
  sfirstorder use:ieq_morphing_mutual, iok_gieq unfold:ieq_good_morphing.
Qed.

Lemma ieq_iok_subst Ξ ℓ ℓ0 b0 b1 a (h : IOk Ξ ℓ0 a) (h0 : IEq (ℓ0:: Ξ) ℓ b0 b1) :
  IEq Ξ ℓ b0[a..] b1[a..].
Proof.
  sfirstorder use:ieq_morphing_mutual, ieq_subst_cons, ieq_subst_id, iok_gieq.
Qed.

Lemma ieq_trans_heterogeneous Ξ ℓ ℓ0 a b c :
  IEq Ξ ℓ a b ->
  IEq Ξ ℓ0 b c ->
  IEq Ξ (ℓ ∩ ℓ0) a c.
Proof.
  move => h0 h1.
  apply ieq_trans with (B := b).
  - apply ieq_sym_mutual.
    apply ieq_sym_mutual in h0.
    eapply ieq_downgrade_mutual; eauto.
  - apply ieq_sym_mutual in h0.
    rewrite meet_commutative.
    eapply ieq_downgrade_mutual; eauto.
Qed.

End geq_facts.
