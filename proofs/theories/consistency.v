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

Lemma ne_contra a ℓ A : nil ⊢ a ; ℓ ∈ A -> ne a -> False.
Proof.
  move E : nil => Γ h.
  move : E.
  elim : Γ ℓ a A /h => //=.
  - hauto lq:on inv:lookup.
  - move => Γ ℓ ℓ0 a A B b ha iha hb ihb ?. subst.
    move /andP => [h0 h1].
    sfirstorder.
  - hauto lqb:on.
  - move => Γ _ ℓ0 ℓ1 i a A h ih _ _ ? ha. subst.
    apply soundness in h.
    move /(_ nil var_tm ltac:(hauto lq:on use:ρ_ok_id)) : h.
    move => [m][PA][]. asimpl. move/InterpUnivN_Void_inv => -> {PA}[_ [v [hr hv]]].
    have ? : v = a by sfirstorder use:nfacts.nf_refl_star. subst.
    tauto.
  - hauto lqb:on.
  - sfirstorder b:on.
Qed.


Lemma consistency a ℓ : ~nil ⊢ a ; ℓ ∈ tVoid.
Proof.
  move => /[dup] h /(proj1 soundness) /(_ nil var_tm ltac:(hauto lq:on use:ρ_ok_id)).
  move => [m][PA][].
  asimpl. move /InterpUnivN_Void_inv => -> {PA}[_ [v [hr hv]]].
  move : subject_reduction_star h hr; repeat move/[apply].
  sfirstorder use:ne_contra.
Qed.

End consistency.
