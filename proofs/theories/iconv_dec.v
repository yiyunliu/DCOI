Require Import imports syntax par conv normalform factorization geq.

Module iconv_dec
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import normalform : normalform_sig lattice syntax par)
  (Import factorization : factorization_sig lattice syntax par normalform)
  (Import conv : conv_sig lattice syntax par ieq).

  Module cfacts := conv_facts lattice syntax par ieq conv.
  Import cfacts.
  Module pfacts := par_facts lattice syntax par.
  Import pfacts.
  Module nfacts := normalform_fact lattice syntax par normalform.
  Import nfacts.

  Definition iconvb Ξ ℓ a b (h0 : wn a) (h1 : wn b) : bool :=
    let a' := LoRed_normalize a h0 in
    let b' := LoRed_normalize b h1 in
    IEqb Ξ ℓ (proj1_sig a') (proj1_sig b').

  Local Lemma nf_refl_star a b (h: a ⇒* b) : (nf a -> b = a).
  Proof.
    elim : a b / h => // ; hauto use:nf_refl b:on.
  Qed.

  Local Lemma confluent_nf a b v (h : a ⇒* b) (h0 : a ⇒* v) (h1 : nf v) :
    b ⇒* v.
  Proof.
    have  : exists v' , b ⇒* v' /\ v ⇒* v' by sfirstorder use:Pars_confluent unfold:confluent.
    hauto l:on use:nf_refl_star.
  Qed.

  Lemma iconv_iconvb Ξ ℓ a b (h0 : wn a) (h1 : wn b) : iconv Ξ ℓ a b -> iconvb Ξ ℓ a b h0 h1.
  Proof.
    rewrite /iconv.
    move => [a0][b0][ha][hb]hab.
    rewrite /iconvb.
    set a' := LoRed_normalize a h0.
    set b' := LoRed_normalize b h1.
    case : a' => va [nfva hva] /=.
    case : b' => vb [nfvb hvb] /=.
    have [] : a0 ⇒* va /\ b0 ⇒* vb by sfirstorder use:confluent_nf.
    move :  hab.
    move /simulation_star => /[apply].
    move => [b1][hb0]hb0'.
    have : b1 ⇒* vb by qauto l:on use:rtc_transitive, confluent_nf.
    move /ifacts.ieq_sym /simulation_star : hb0' => /[apply].
    move => [b'][?]h.
    have ? : b' = va by sfirstorder use:nf_refl_star. subst => _.
    move : h. sfirstorder use:ifacts.IEq_IEqb, ifacts.ieq_sym.
  Qed.

  Lemma iconvb_iconv Ξ ℓ a b (h0 : wn a) (h1 : wn b) : iconvb Ξ ℓ a b h0 h1 -> iconv Ξ ℓ a b.
  Proof.
    rewrite /iconvb /iconv.
    set a' := LoRed_normalize a h0.
    set b' := LoRed_normalize b h1.
    case : a' => va [nfva hva] /=.
    case : b' => vb [nfvb hvb] /=.
    move /ifacts.IEqb_IEq.
    hauto lq:on.
  Qed.

  Lemma iconv_dec Ξ ℓ a b (h0 : wn a) (h1 : wn b) : Bool.reflect (iconv Ξ ℓ a b) (iconvb Ξ ℓ a b h0 h1).
  Proof. hauto l:on use:Bool.iff_reflect, iconvb_iconv, iconv_iconvb. Qed.

End iconv_dec.
