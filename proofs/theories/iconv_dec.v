Require Import typing imports syntax par conv normalform factorization geq soundness semtyping preservation.

Module Type LatticeWithBot
  (Import lattice : Lattice).
  Parameter bot : T.
  Axiom bot_prop : forall a, meet bot a = bot.
End LatticeWithBot.

Module conv_dec_bot
  (Import lattice : Lattice)
  (Import bot : LatticeWithBot lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import normalform : normalform_sig lattice syntax par)
  (Import factorization : factorization_sig lattice syntax par normalform)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv)
  (Import lr : lr_sig lattice syntax par normalform ieq conv).

  Module soundness := soundness lattice syntax par normalform ieq conv typing lr.
  Import soundness.
  Module Solver := Solver lattice.
  Import Solver.
  Module preservation := preservation lattice syntax par ieq conv typing.
  Import preservation.
  Import cfacts.

  Fixpoint compute_level (Ξ : econtext) a : T :=
    match a with
    | var_tm i => nth_default bot Ξ i
    | tApp a ℓ0 b => compute_level Ξ a
    | tAbs ℓ0 a => compute_level (ℓ0 :: Ξ) a
    | tJ ℓp t p => compute_level Ξ t ∪ ℓp
    | tEq ℓ0 a b => ℓ0
    | tRefl => bot
    | tVoid => bot
    | tUniv _ => bot
    | tAbsurd _ => bot
    | tPi ℓ0 A B => compute_level Ξ A ∪ compute_level (ℓ0::Ξ) B
    | tSig ℓ0 A B => compute_level Ξ A ∪ compute_level (ℓ0::Ξ) B
    | tPack ℓ0 a b => compute_level Ξ b
    | tLet ℓ0 ℓ1 a b => compute_level (ℓ1::ℓ0::Ξ) b ∪ ℓ1
    | tZero => bot
    | tSuc a => compute_level Ξ a
    | tInd ℓ0 a b c => ℓ0
    | tNat => bot
    | tTT => bot
    | tSeq ℓ0 a b => ℓ0 ∪ compute_level Ξ b
    | tUnit => bot
    end.

  Module ifacts := geq_facts lattice syntax ieq.
  Import ifacts.

  Ltac solve_lattice_with_bot :=
      ltac2:(solve_lattice); try rewrite !meet_idempotent; have := bot_prop; by firstorder.

  Lemma compute_level_is_min (Ξ : econtext) a ℓ :
    IOk Ξ ℓ a -> compute_level Ξ a ⊆ ℓ.
  Proof.
    move => h. elim : Ξ ℓ a /h => //= ;
       lazymatch goal with
       | [ |- context[elookup]] => rewrite /elookup /nth_default => > -> //
       | _ => try hauto lq:on solve+:solve_lattice_with_bot
       end.
  Qed.

  Local Hint Constructors IOk : iok.

  Lemma compute_level_downgrade (Ξ : econtext) a ℓ :
    IOk Ξ ℓ a -> IOk Ξ (compute_level Ξ a) a.
  Proof.
    move => h.
    elim : Ξ ℓ a /h => //=; eauto with iok;
      lazymatch goal with
      | [ |- context[elookup]] => hauto lq:on use:IO_Var unfold:elookup, nth_default solve+:solve_lattice
      | _ => hauto lq:on use:iok_subsumption ctrs:IOk solve+:solve_lattice
      end.
  Qed.

  Definition convb {ℓ ℓ0 i a} Γ A B (h0 : Γ ⊢ a ; ℓ ∈ A) (h1 : Γ ⊢ B ; ℓ0 ∈ tUniv i ) : bool :=
    let Ξ := c2e Γ in
    let A' := proj1_sig (LoRed_normalize A ltac:(hauto q:on use:normalization, Wt_regularity)) in
    let B' := proj1_sig (LoRed_normalize B ltac:(hauto lq:on use:normalization)) in
    IEqb Ξ (compute_level Ξ A') A' B'.

  Lemma convb_conv {ℓ ℓ0 i a} Γ A B (h0 : Γ ⊢ a ; ℓ ∈ A) (h1 : Γ ⊢ B ; ℓ0 ∈ tUniv i) :
    convb Γ A B h0 h1 -> conv (c2e Γ) A B.
  Proof.
    rewrite /convb.
    case : (LoRed_normalize A _) => A' [hA'0 hA'1].
    case : (LoRed_normalize B _) => B' [hB'0 hB'1] /= h.
    set ℓmin := (compute_level _ _) in h.
    rewrite /conv /iconv.
    exists ℓmin, A', B'.
    repeat split => //=.
    eauto using IEqb_IEq.
  Qed.

  Lemma conv_convb {ℓ ℓ0 i a} Γ A B (h0 : Γ ⊢ a ; ℓ ∈ A) (h1 : Γ ⊢ B ; ℓ0 ∈ tUniv i) :
    conv (c2e Γ) A B -> convb Γ A B h0 h1.
  Proof.
    rewrite /convb => h.
    case : (LoRed_normalize A _) => vA' [hvA0 hvA1].
    case : (LoRed_normalize B _) => vB' [hvB0 hvB1] /=.
    apply IEq_IEqb.
    have {}h: conv (c2e Γ) vA' vB' by eauto using conv_par_star2.
    rewrite /conv /iconv in h.
    move : h => [ℓ'][x][y][?][?]h.
    have [? ?] : x = vA' /\ y = vB' by sfirstorder use:nfact.nf_refl_star. subst.
    have [? ?] : exists ℓA, IOk (c2e Γ) ℓA vA' by
        apply Wt_regularity in h0; hauto lq:on use:tcfacts.typing_iok, cfacts.iok_preservation_star.
    have ? : IOk (c2e Γ) ℓ0 vB' by hauto lq:on use:tcfacts.typing_iok, cfacts.iok_preservation_star.
    set ℓA := compute_level _ vA'.
    have hA : IOk (c2e Γ) ℓA vA' by sfirstorder use:compute_level_downgrade.
    have ? : IOk (c2e Γ) (ℓA ∩ ℓ') vA' by sfirstorder use:iok_ieq_downgrade_iok.
    have h2 : ℓA ⊆ ℓA ∩ ℓ' by sfirstorder use:compute_level_is_min.
    have {}h2: ℓA ⊆ ℓ' by solve_lattice.
    sfirstorder use:iok_ieq_downgrade.
  Qed.

  Lemma conv_dec {ℓ ℓ0 i a} Γ A B (h0 : Γ ⊢ a ; ℓ ∈ A) (h1 : Γ ⊢ B ; ℓ0 ∈ tUniv i) :
    Bool.reflect (conv (c2e Γ) A B) (convb Γ A B h0 h1).
  Proof. hauto l:on use:Bool.iff_reflect, convb_conv, conv_convb. Qed.

End conv_dec_bot.

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

  Lemma iconv_iconvb Ξ ℓ a b (h0 : wn a) (h1 : wn b) : iconv Ξ ℓ a b -> iconvb Ξ ℓ a b h0 h1.
  Proof.
    move => h.
    rewrite /iconvb.
    case : LoRed_normalize =>//= va [hva0 hva1].
    case : LoRed_normalize =>//= vb [hvb0 hvb1].
    have {}h : iconv Ξ ℓ va vb by hauto lq:on use:iconv_par_star2.
    move : h => [va'][vb']?.
    have [? ?] : va' = va /\ vb' = vb by sfirstorder use:nf_refl_star. subst.
    apply ifacts.IEq_IEqb. tauto.
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
