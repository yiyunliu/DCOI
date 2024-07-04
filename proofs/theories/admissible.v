Require Import conv par geq imports typing typing_conv preservation.

Module admissible
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv).

Module preservation := preservation lattice syntax par ieq conv typing.
Import preservation.

Module cfacts := conv_facts lattice syntax par ieq conv.
Import cfacts.

Module ifacts := cfacts.ifacts.
Import ifacts.

Module tcfacts := typing_conv_facts lattice syntax par ieq conv typing.
Import tcfacts.

Import pfacts.

Module solver := Solver lattice.
Import solver.

(* Downgrade operator *)

Lemma T_Down_Alt Γ ℓ ℓ0 ℓ1 a b A p :
  ℓ1 ⊆ ℓ0 ->
  Γ ⊢ a ; ℓ1 ∈ A ->
  Γ ⊢ b ; ℓ1 ∈ A ->
  Γ ⊢ p ; ℓ ∈ tEq ℓ0 a b ->
  (* --------------------- *)
  Γ ⊢ tJ ℓ tRefl p ; ℓ ∈ tEq ℓ1 a b.
Proof.
  move => hℓ ha hb hp.
  have -> : tEq ℓ1 a b = (tEq ℓ1 (ren_tm S (ren_tm S a)) (var_tm 1))[p .: b..] by asimpl.
  apply T_J_simpl with (a := a) (A := A) (i := 0) (ℓp := ℓ) (ℓ0 := ℓ0) (ℓ1 := ℓ1); eauto.
  solve_lattice.
  - move => [:hwff].
    eapply T_Eq; eauto.
    asimpl.
    + apply renaming_Syn with (Γ := Γ) => //; eauto.
      * rewrite /lookup_good_renaming.
        move => i ℓ2 A0.
        move => h. exists ℓ2.
        split; last by solve_lattice.
        apply : there'; cycle 1.
        apply : there'; eauto.
        by asimpl.
      * abstract : hwff.
        move /Wt_regularity : (ha) => [ℓA][i]hA.
        apply Wff_cons with (i := 0) (ℓ := ℓ0).
        by eauto using Wff_cons with wff.
        eapply T_Eq_simpl;eauto.
        apply : weakening_Syn; eauto.
        sfirstorder use:subsumption.
        apply : T_Var; eauto using here with wff.
    + apply : T_Var; eauto.
      apply : there'; eauto;cycle 1. by apply here.
      by asimpl.
      solve_lattice.
  - asimpl. eapply T_Refl; eauto with wff.
Qed.

(* Box types *)

Lemma T_T Γ ℓ ℓ0 i A :
  Γ ⊢ A ; ℓ ∈ tUniv i ->
  (* ------------------------------------------ *)
  Γ ⊢ tSig ℓ0 A (tPi ℓ0 tVoid tVoid) ; ℓ ∈ tUniv i.
Proof.
  move => h.
  replace i with (max i i) by apply PeanoNat.Nat.max_id.
  apply T_Sig => //.
  replace i with (max i i) by apply PeanoNat.Nat.max_id.
  apply T_Pi.
  hauto lq:on ctrs:Wt,Wff use:Wt_Wff.
  apply T_Void.
  hauto lq:on ctrs:Wt,Wff use:Wt_Wff.
Qed.

Lemma T_Box Γ ℓ ℓ0 a A :
  Γ ⊢ a ; ℓ0 ∈ A ->
  (* ----------------------------------------------------------------------------- *)
  Γ ⊢ tPack ℓ0 a (tAbs ℓ0 (tAbsurd (var_tm 0))) ; ℓ ∈ tSig ℓ0 A (tPi ℓ0 tVoid tVoid).
Proof.
  move => /[dup] /Wt_regularity => [[ℓ1]] [j] hA ha.
  apply : T_Pack => //.
  - asimpl.
    apply T_Abs_simpl.
    apply : T_Absurd.
    apply : T_Var; eauto using meet_idempotent.
    hauto lq:on ctrs:Wt,Wff use:Wt_Wff.
    apply here.
    apply T_Void.
    hauto lq:on ctrs:Wt,Wff use:Wt_Wff.
  - apply T_Sig with (ℓ := ℓ1) (i := j) => //.
    apply T_Pi. hauto lq:on ctrs:Wt,Wff use:Wt_Wff.
    apply T_Void. hauto lq:on ctrs:Wt,Wff use:Wt_Wff.
  Unshelve. exact ℓ0. all: exact 0.
Qed.

Lemma T_Unbox Γ ℓ ℓ0 a A :
  ℓ0 ⊆ ℓ ->
  Γ ⊢ a ; ℓ ∈ tSig ℓ0 A (tPi ℓ0 tVoid tVoid) ->
  (* --------------------------------------- *)
  Γ ⊢ tLet ℓ0 ℓ a (var_tm 1) ; ℓ ∈ A.
Proof.
  move => hℓ /[dup] /Wt_regularity => [[?]] [?] /[dup] /Wt_Sig_inv => [[i]] [j] [hA] [hB] _ hSig ha.
  replace A with (ren_tm S A)[a..]; last by asimpl.
  eapply T_Let_simpl with (A := A); eauto using meet_idempotent.
  - asimpl. apply : T_Var; eauto using hℓ.
    hauto lq:on ctrs:Wt,Wff use:Wt_Wff.
    apply : there'; cycle 1.
    apply here. substify. by asimpl.
  - eapply weakening_Syn in hA.
    asimpl in hA. all: eassumption.
Qed.

(* Pair projections *)

Lemma T_Proj1 Γ ℓ ℓ0 ℓ1 a A B :
  ℓ0 ⊆ ℓ ->
  ℓ1 ⊆ ℓ ->
  Γ ⊢ a ; ℓ1 ∈ tSig ℓ0 A B ->
  (* ------------------------------*)
  Γ ⊢ tLet ℓ0 ℓ1 a (var_tm 1) ; ℓ ∈ A.
Proof.
  move => hℓ hℓ' /[dup] /Wt_regularity => [[?]] [?] /[dup] /Wt_Sig_inv => [[i]] [j] [hA] [hB] _ hSig h.
  replace A with (ren_tm S A)[a..]; last by asimpl.
  eapply T_Let_simpl ; eauto using meet_idempotent.
  - apply : T_Var; last by apply hℓ.
    + hauto lq:on ctrs:Wff use:Wt_Wff.
    + apply : there'; cycle 1.
      apply here. substify. by asimpl.
  - eauto using weakening_Syn_Univ. 
Qed.

Lemma T_Proj2 Γ ℓ ℓ0 ℓ1 a A B :
  ℓ1 ⊆ ℓ ->
  ℓ1 ⊆ ℓ0 ->
  Γ ⊢ tLet ℓ0 ℓ1 a (var_tm 1) ; ℓ0 ∈ A ->
  Γ ⊢ a ; ℓ1 ∈ tSig ℓ0 A B ->
  (* ---------------------------------------------------------- *)
  Γ ⊢ tLet ℓ0 ℓ1 a (var_tm 0) ; ℓ ∈ B[(tLet ℓ0 ℓ1 a (var_tm 1))..].
Proof.
  move => hℓ hℓ' hLet /[dup] /Wt_regularity => [[ℓ4]] [k] /[dup] /Wt_Sig_inv => [[i]] [j] [hA] [hB] _ hSig h.
  replace B[(tLet ℓ0 ℓ1 a (var_tm 1))..]
    with (B[(tLet ℓ0 ℓ1 (var_tm 0) (var_tm 1)) .: shift >> var_tm])[a..];
    last by asimpl.
  have ? : ⊢ (ℓ0, A) :: Γ by eauto with wff.
  have ? : ⊢ (ℓ1, B) :: (ℓ0, A) :: Γ by eauto with wff.
  eapply T_Let_simpl with (ℓT := ℓ4) (i := j); eauto using meet_idempotent.
  - move => [:eqb].
    asimpl.
    eapply T_Conv with (A := B ⟨S⟩) (i := j).
    apply : T_Var; eauto.
    + apply here'. reflexivity.
    + eapply morphing_Syn_Univ; eauto.
      apply good_morphing_cons.
      * have -> : (S >> (S >> var_tm)) = var_tm >> ren_tm S >> ren_tm S by asimpl.
        hauto lq:on use:good_morphing_suc, good_morphing_nil db:wff.
      * apply : T_Proj1; eauto. solve_lattice.
        apply : T_Pack; eauto.
        apply : T_Var => //.
        apply : there'; cycle 1.
        by apply here.
        by substify; asimpl.
        solve_lattice.
        apply : T_Var=>//.
        apply here'.
        2 : { solve_lattice. }
        2 : { 
          suff : (ℓ1, B)::(ℓ0, A)::Γ ⊢ (tSig ℓ0 A B)⟨S⟩⟨S⟩; ℓ4 ∈ tUniv k.
          substify; asimpl.  apply.
          eapply weakening_Syn_Univ; eauto.
          eapply weakening_Syn_Univ; eauto.
        }
        asimpl.
        abstract : eqb.
        substify.
        f_equal. fext. elim => //=.
    + move => //=.
      exists ℓ4. apply iconv_sym.
      apply iconv_rpar with (a := B ⟨S⟩).
      apply ieq_iconv.
      apply iok_ieq with (ℓ := ℓ4).
      have : (ℓ1, B) :: (ℓ0, A):: Γ ⊢ B ⟨S⟩; ℓ4 ∈ tUniv j by
        sfirstorder use:weakening_Syn_Univ.
      move/typing_iok => //=.
      solve_lattice.
      have hr : tLet ℓ0 ℓ1 (tPack ℓ0 (var_tm 1) (var_tm 0)) (var_tm 1) ⇒ var_tm 1 by apply P_LetPackCBN'; asimpl.
      rewrite -eqb.
      apply Par_morphing; last by apply Par_refl.
      hauto lq:on ctrs:Par inv:nat unfold:Par_m.
  - move => [:tr0].
    apply : morphing_Syn_Univ; eauto; last by abstract :tr0; hauto lq:on db:wff.
    rewrite /lookup_good_morphing.
    move => i0 ℓ2 A0.
    elim/lookup_inv => //= _.
    + move => ℓ3 A1 Γ0 ? [*]. subst.
      apply : T_Proj1=>//. solve_lattice.
      apply : T_Var; eauto.
      apply here'.
      asimpl. substify. eauto.
      solve_lattice.
    + move => n A1 Γ0 ℓ3 B0 ? ? [*]. subst.
      asimpl.
      have -> :  var_tm (S n) = (var_tm n)⟨S⟩ by asimpl.
      renamify.
      apply : weakening_Syn; eauto.
      apply : T_Var; eauto. eauto with wff. solve_lattice.
Qed.

(* I think this version holds too but I'm not sure? *)
Lemma T_Proj2_Alt Γ ℓ ℓ0 ℓ1 a A B :
  ℓ1 ⊆ ℓ ->
  Γ ⊢ a ; ℓ1 ∈ tSig ℓ0 A B ->
  (* ------------------------------------------------------ *)
  Γ ⊢ tLet ℓ0 ℓ1 a (var_tm 0) ; ℓ ∈ tLet ℓ0 ℓ1 a B[(var_tm 1) .: shift >> shift >> var_tm].
Proof.
  move => ? /[dup] /Wt_regularity => [[ℓB]] [?] /[dup] /Wt_Sig_inv => [[i]] [j] [hA] [hB] _ hSig h.
  have -> : (tLet ℓ0 ℓ1 a B[(var_tm 1) .: shift >> shift >> var_tm])
    = (tLet ℓ0 ℓ1 (var_tm 0) B[var_tm 1 .: shift >> shift >> shift >> var_tm])[a..]
    by asimpl.
  have ? : ⊢ (ℓ1, tSig ℓ0 A B) :: Γ by hauto lq:on db:wff.
  set q := ℓ1 ∪ ℓB.
  have hℓ' : ℓ1 ⊆ q by subst q; solve_lattice.
  have hℓ'' : ℓB ⊆ q by subst q; solve_lattice.
  eapply T_Let_simpl => //.
  - eauto.
  - move => [:hwff].
    eapply T_Conv with (A := B ⟨S⟩) (i := j).
    + apply : T_Var.
      * abstract : hwff; hauto lq:on ctrs:Wff use:Wt_Wff.
      * apply here'. reflexivity.
      * assumption.
    + eapply morphing_Syn_Univ; eauto; cycle 1.
      apply good_morphing_cons with (A := tSig ℓ0 A B) (ℓ := ℓ1).
      * asimpl.
        have -> : (S >> (S >> var_tm)) = var_tm >> ren_tm S >> ren_tm S by asimpl.
        hauto lq:on use:good_morphing_suc, good_morphing_nil db:wff.
      * asimpl.
        apply : T_Pack.
        ** apply : T_Var; eauto.
           apply : there'; cycle 1.
           apply : here'; eauto.
           substify. by asimpl.
           solve_lattice.
        ** apply : T_Var; eauto.
           apply : here'. asimpl. substify. 
           have -> // : var_tm 1 .: S >> (S >> var_tm) = S >> var_tm
             by fext; case.
           solve_lattice.
        ** replace (tSig ℓ0 _ _) with ((tSig ℓ0 A B)[(S >> S) >> var_tm]); last by asimpl.
           eapply weakening_Syn in hSig; last by exact hA.
           eapply weakening_Syn in hSig; last by exact hB.
           replace (tSig ℓ0 A B) [(S >> S) >> var_tm] with (tSig ℓ0 A B) ⟨S⟩ ⟨S⟩;
            last by substify; asimpl.
           exact hSig.
      * eapply T_Let_simpl' with (C := tUniv j) => //=.
        ** apply hℓ'.
        ** apply : T_Var; eauto.
           apply here'. eauto.
           solve_lattice.
        ** rewrite -/ren_tm.
           asimpl.
           have -> : B [var_tm 1 .: S >> (S >> (S >> var_tm))] =
                      B ⟨1 .: S >> (S >> S)⟩ by substify; asimpl.
           apply : renaming_Syn_Univ; eauto using subsumption.
           rewrite /lookup_good_renaming.
           move => i0 ℓ2 A0.
           elim /lookup_inv => _ //=.
        *** move => ℓ3 A1 Γ0 ? [*]. subst.
           eexists. split. apply : there'; cycle 1.
           apply here.
           by asimpl.
           solve_lattice.
        *** move => n A1 Γ0 ℓ3 B0 ? ? [*]. subst.
           eexists.
           asimpl. split.
           apply : there'; cycle 1.
           apply : there'; cycle 1.
           apply : there'; cycle 1.
           eauto.
           eauto.
           eauto.
           by asimpl.
           solve_lattice.
        *** have E : A ⟨S⟩ = A[S >> var_tm] by substify.
            have -> : B ⟨0 .: S >> S⟩ = B[var_tm 0 .: S >> S >> var_tm] by substify; asimpl.
            have hA' : (ℓ1, tSig ℓ0 A B) :: Γ ⊢ A[S >> var_tm]; ℓB ∈ tUniv i.
            { eapply weakening_Syn in hA.
              rewrite E in hA. exact hA. exact hSig. }
            have hwff' : ⊢ (ℓ0, A[S >> var_tm]) :: (ℓ1, tSig ℓ0 A B) :: Γ
              by hauto lq:on ctrs:Wff use:Wff_cons, Wt_Wff.
            rewrite E.
            apply : Wff_cons => //.
            eapply morphing_Syn_Univ
              with (ρ := var_tm 0 .: S >> S >> var_tm)
                   (Δ := (ℓ0, A[S >> var_tm]) :: (ℓ1, tSig ℓ0 A B) :: Γ)
              in hB => //.
            exact hB. asimpl.
            have -> : (S >> (S >> var_tm)) = var_tm >> ren_tm S >> ren_tm S by asimpl.
            apply good_morphing_cons.
            apply : good_morphing_suc; eauto.
            apply : good_morphing_suc; eauto.
            hauto lq:on rew:off use:good_morphing_nil, Wt_Wff.
            apply : T_Var; auto using meet_idempotent.
            apply here'. by asimpl.
        ** rewrite -/ren_tm.
           apply T_Univ => //.
           admit.
    + asimpl.
      exists q.
      apply cfacts.iconv_sym.
      apply : cfacts.iconv_rpar; cycle 1.
      apply P_LetPackCBN'; eauto.
      asimpl.
      apply cfacts.ieq_iconv.
      have -> : var_tm 1 .: (S >> (S >> var_tm)) = S >> var_tm by fext; elim => //=.
      renamify.
      apply iok_ieq with (ℓ := q).
      apply : typing_iok. eauto. apply : weakening_Syn_Univ; eauto using subsumption.
      solve_lattice.
  - eapply T_Let_simpl' with (C := tUniv i); eauto using meet_idempotent.
    + apply : T_Var; eauto.
      apply here'; eauto.
      solve_lattice.
    + rewrite -/ren_tm.
      Set Printing All.
      admit.
    + apply T_Univ. admit.
Admitted.

End admissible.