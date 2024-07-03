Require Import conv par geq imports semtyping typing typing_conv normalform soundness preservation.

Module consistency
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import nf : normalform_sig lattice syntax par)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv)
  (Import lr : lr_sig lattice syntax par nf ieq conv).

Module soundness := soundness lattice syntax par nf ieq conv typing lr.
Module preservation := preservation lattice syntax par ieq conv typing.
Import soundness.
Import preservation.

Fixpoint debruijnDepth a : nat :=
  match a with
  | var_tm i => 1 + i
  | tAbs _ b => debruijnDepth b - 1
  | tApp a _ b => max (debruijnDepth a) (debruijnDepth b)
  | tPi _ A B => max (debruijnDepth A) (debruijnDepth B - 1)
  | tSig _ A B => max (debruijnDepth A) (debruijnDepth B - 1)
  | tUniv _ => 0
  | tEq _ a b => max (debruijnDepth a) (debruijnDepth b)
  | tRefl => 0
  | tJ _ t p => max (debruijnDepth t - 2) (debruijnDepth p)
  | tVoid => 0
  | tLet _ _ a b => max (debruijnDepth a) (debruijnDepth b - 2)
  | tPack _ a b => max (debruijnDepth a) (debruijnDepth b)
  | tAbsurd => 0
  end.

Lemma lookup_lt i Γ ℓ A : lookup i Γ ℓ A -> i < length Γ.
Proof. induction 1; sfirstorder. Qed.

Lemma wt_dbound Γ ℓ a A : Γ ⊢ a ; ℓ ∈ A -> debruijnDepth a <= length Γ.
Proof.
  move => h.
  elim : Γ ℓ a A / h => /=; try lia.
  hauto lq:on use:lookup_lt.
Qed.

Fixpoint hasAbsurd a :=
  match a with
  | var_tm i => false
  | tAbs _ b => false
  | tApp a _ b => hasAbsurd a || hasAbsurd b
  | tPi _ A B => hasAbsurd A
  | tSig _ A B => hasAbsurd A
  | tUniv _ => false
  | tEq _ a b => hasAbsurd a || hasAbsurd b
  | tRefl => false
  | tJ _ t p => hasAbsurd t || hasAbsurd p
  | tVoid => false
  | tLet _ _ a b => hasAbsurd a
  | tPack _ a b => hasAbsurd a || hasAbsurd b
  | tAbsurd => true
  end.

Lemma ne_depth_gt0 a : ne a -> debruijnDepth a > 0 \/ hasAbsurd a.
  elim : a => //=; try lia; sfirstorder b:on.
Qed.

(* Lemma par_absurd_exp a b : a ⇒ b -> hasAbsurd b -> hasAbsurd a. *)
(* Proof. *)
(*   move => h. elim : a b /h => //=. *)
(*   - sfirstorder b:on. *)
(*   - admit. *)
(*   - sfirstorder b:on. *)
(*   - sfirstorder b:on. *)
(*   - sfirstorder b:on. *)
(*   - sfirstorder b:on. *)
(*   - move => _ _ a0 b0 c0 a1 b1 c1 ha iha hb ihb hc ihc. *)



Lemma ne_ill_type_void ℓ a A : nil ⊢ a ; ℓ ∈ A -> hasAbsurd a -> False.
  move E : (nil) => Γ h.
  move : E.
  elim : Γ ℓ a A /h => //=.
  - sfirstorder b:on.
  - move => Γ _ ℓ0 ℓ1 i a A ha iha _ _ ? _. subst.
    move : ha  =>  /[dup] ha /(proj1 soundness) /(_ nil var_tm ltac:(hauto lq:on use:ρ_ok_id)).
    move => [m][PA][].
    asimpl. move /InterpUnivN_Void_inv => -> {PA}[_ [v [hr hv]]].
    suff : hasAbsurd a by tauto.
    have hv' : nil ⊢ v ; ℓ0 ∈ tVoid by sfirstorder use:subject_reduction_star.
    move /wt_dbound in hv'.
    simpl in hv'.
    have {}hv' : hasAbsurd v by qauto l:on use:ne_depth_gt0 solve+:lia.

    have : hasAbsurd v by , ne_depth_gt0.
  - sfirstorder b:on.
  - sfirstorder b:on.


(* Lemma ne_ill_type a ℓ A : nil ⊢ a ; ℓ ∈ A -> ne a \/ A = tVoid -> False. *)
(* Proof. *)
  (* move E : nil=> Γ h. *)
  (* move : E. *)
  (* elim : Γ ℓ a A / h => //=. *)
  (* - hauto lq:on inv:lookup. *)
  (* - sfirstorder. *)
  (* - sfirstorder. *)
  (* - best. *)
  (* - sfirstorder lqb:on. *)
  (* - move => Γ _ ℓ0 ℓ1 i a A ha iha hA ? ?. subst. *)
  (*   move /(proj1 soundness) /(_ nil var_tm ltac:(hauto lq:on use:ρ_ok_id)) : ha. *)
(*   move => [m][PA][]. asimpl. move /InterpUnivN_Void_inv => -> {PA}[_ [v [hr hv]]]. *)

Lemma consistency a ℓ : ~nil ⊢ a ; ℓ ∈ tVoid.
Proof.
  move => /[dup] h /(proj1 soundness) /(_ nil var_tm ltac:(hauto lq:on use:ρ_ok_id)).
  move => [m][PA][].
  asimpl. move /InterpUnivN_Void_inv => -> {PA}[_ [v [hr hv]]].
  move : subject_reduction_star h hr; repeat move/[apply].
  move /wt_dbound => //=.
  move /ne_depth_gt0 : (hv).
  case => //=. lia.

  case : v hv => //=; try lia.
  move /ne_depth_gt0 : hv => /=. lia.
Qed.

End consistency.
