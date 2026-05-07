Require Import conv par geq imports normalform.

Module Type lr_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import nf : normalform_sig lattice syntax par)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq).

Module pfacts := par_facts lattice syntax par.
Import pfacts.

Module cfacts := conv_facts lattice syntax par ieq conv.
Import cfacts.

Module nfacts := normalform_fact lattice syntax par nf.
Import nfacts.

(** Generic predicates over labelled-typed terms. They are used in the
    statement of the introduction rules, so they live above the abstract
    [LogRel] interface. *)

Definition ProdSpace Ξ ℓ0 (PA : T -> tm -> Prop) (PF : tm -> (T -> tm -> Prop) -> Prop)ℓ (b : tm) :=
  IOk Ξ ℓ b /\
  forall a PB, PA ℓ0 a -> PF a PB -> PB ℓ (tApp b ℓ0 a).

Definition SumSpace Ξ ℓ0 (PA : T -> tm -> Prop) (PF : tm -> (T -> tm -> Prop) -> Prop)ℓ (t : tm) :=
  IOk Ξ ℓ t /\
  ((exists a b, t ⇒* tPack ℓ0 a b /\ PA ℓ0 a /\ (forall PB, PF a PB -> PB ℓ b)) \/ wne t).

(* P identifies a set of "reducibility candidates" *)
Definition CR Ξ (P : T -> tm -> Prop) :=
  (forall ℓ a, P ℓ a -> wn a) /\
    (forall ℓ a, wne a -> IOk Ξ ℓ a -> P ℓ a).

Lemma wne_var Ξ ℓ :
  let tD := tAbsurd tVoid in
  wne tD /\ IOk Ξ ℓ tD.
Proof. hauto lq:on ctrs:rtc, IOk. Qed.

(** ** Abstract logical relation interface

    [LogRel] declares the logical predicate [InterpUnivN] together with
    its introduction rules and a custom induction principle. The
    encoding (an inner inductive [InterpExt] tied through Equations) is
    an implementation detail of [LogRelImpl] below; consumers of
    [LogRel] never see it. *)
Module Type LogRel.

  Parameter InterpUnivN : econtext -> nat -> tm -> (T -> tm -> Prop) -> Prop.

  Notation " ⟦ Ξ ⊨ A ⟧ i  ↘ S" := (InterpUnivN Ξ i A S)
                                    (at level 70, no associativity).

  (** Introduction rules *)

  Axiom InterpUnivN_Ne : forall Ξ i A,
    ne A ->
    ⟦ Ξ ⊨ A ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).

  Axiom InterpUnivN_Nat : forall Ξ i,
    ⟦ Ξ ⊨ tNat ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v).

  Axiom InterpUnivN_Fun : forall Ξ i ℓ0 A B PA PF,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
    (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ ProdSpace Ξ ℓ0 PA PF.

  Axiom InterpUnivN_Univ : forall Ξ i j,
    j < i ->
    ⟦ Ξ ⊨ tUniv j ⟧ i ↘ (fun ℓ A => IOk Ξ ℓ A /\ exists PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA).

  Axiom InterpUnivN_Void : forall Ξ i,
    ⟦ Ξ ⊨ tVoid ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).

  Axiom InterpUnivN_Eq_nf : forall Ξ i ℓ0 a b,
    nf a -> nf b ->
    ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘
      (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).

  Axiom InterpUnivN_Sig : forall Ξ i ℓ0 A B PA PF,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
    (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ SumSpace Ξ ℓ0 PA PF.

  Axiom InterpUnivN_Step : forall Ξ i A A0 PA,
    A ⇒ A0 -> ⟦ Ξ ⊨ A0 ⟧ i ↘ PA -> ⟦ Ξ ⊨ A ⟧ i ↘ PA.

  Axiom InterpUnivN_Unit : forall Ξ i,
    ⟦ Ξ ⊨ tUnit ⟧ i ↘
      (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (v = tTT \/ ne v)).

  (** Custom induction principle: doesn't expose [InterpExt] *)
  Axiom InterpUnivN_ind : forall Ξ (P : nat -> tm -> (T -> tm -> Prop) -> Prop),
    (forall i A, ne A ->
       P i A (fun ℓ a => IOk Ξ ℓ a /\ wne a)) ->
    (forall i,
       P i tNat (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v)) ->
    (forall i ℓ0 A B PA PF,
       ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
       P i A PA ->
       (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> P i B[a..] PB) ->
       P i (tPi ℓ0 A B) (ProdSpace Ξ ℓ0 PA PF)) ->
    (forall i j, j < i ->
       (forall A PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA -> P j A PA) ->
       P i (tUniv j) (fun ℓ A => IOk Ξ ℓ A /\ exists PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA)) ->
    (forall i,
       P i tVoid (fun ℓ a => IOk Ξ ℓ a /\ wne a)) ->
    (forall i ℓ0 a b, nf a -> nf b ->
       P i (tEq ℓ0 a b)
         (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p))) ->
    (forall i ℓ0 A B PA PF,
       ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
       P i A PA ->
       (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> P i B[a..] PB) ->
       P i (tSig ℓ0 A B) (SumSpace Ξ ℓ0 PA PF)) ->
    (forall i A A0 PA,
       A ⇒ A0 -> ⟦ Ξ ⊨ A0 ⟧ i ↘ PA -> P i A0 PA -> P i A PA) ->
    (forall i,
       P i tUnit (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (v = tTT \/ ne v))) ->
    forall i A PA, ⟦ Ξ ⊨ A ⟧ i ↘ PA -> P i A PA.

End LogRel.

(** ** Derived facts over [LogRel] *)
Module Type LogRelFacts (M : LogRel).
  Import M.

  Axiom InterpUnivN_Fun_nopf : forall Ξ i ℓ0 A B PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ (ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB)).

  Axiom InterpUnivN_Sig_nopf : forall Ξ i ℓ0 A B PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ (SumSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB)).

  Axiom InterpUnivN_cumulative : forall Ξ i A PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> forall j, i <= j ->
    ⟦ Ξ ⊨ A ⟧ j ↘ PA.

  Axiom InterpUnivN_preservation : forall Ξ i A B P,
    ⟦ Ξ ⊨ A ⟧ i ↘ P -> A ⇒ B -> ⟦ Ξ ⊨ B ⟧ i ↘ P.

  Axiom InterpUnivN_preservation_star : forall Ξ i A B P,
    ⟦ Ξ ⊨ A ⟧ i ↘ P -> A ⇒* B -> ⟦ Ξ ⊨ B ⟧ i ↘ P.

  Axiom InterpUnivN_back_preservation_star : forall Ξ i A B P,
    ⟦ Ξ ⊨ B ⟧ i ↘ P -> A ⇒* B -> ⟦ Ξ ⊨ A ⟧ i ↘ P.

  Axiom InterpUnivN_subsumption : forall Ξ i A P,
    ⟦ Ξ ⊨ A ⟧ i ↘ P ->
    forall ℓ ℓ0 a, ℓ ⊆ ℓ0 -> P ℓ a -> P ℓ0 a.

  Axiom InterpUnivN_Ne_inv : forall Ξ i A P,
    ne A ->
    ⟦ Ξ ⊨ A ⟧ i ↘ P ->
    P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).

  Axiom InterpUnivN_Nat_inv : forall Ξ i P,
    ⟦ Ξ ⊨ tNat ⟧ i ↘ P ->
    P = fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v.

  Axiom InterpUnivN_Eq_inv : forall Ξ i ℓ0 a b P,
    ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘ P ->
    P = (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).

  Axiom InterpUnivN_Void_inv : forall Ξ i P,
    ⟦ Ξ ⊨ tVoid ⟧ i ↘ P -> P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).

  Axiom InterpUnivN_Unit_inv : forall Ξ i P,
    ⟦ Ξ ⊨ tUnit ⟧ i ↘ P ->
    P = fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (v = tTT \/ ne v).

  Axiom InterpUnivN_Univ_inv : forall Ξ i j P,
    ⟦ Ξ ⊨ tUniv j ⟧ i ↘ P ->
    P = (fun ℓ0 A => IOk Ξ ℓ0 A /\ exists PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA) /\ j < i.

  Axiom InterpUnivN_Fun_inv_nopf : forall Ξ i ℓ0 A B P,
    ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ P ->
    exists PA,
      ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
      (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB).

  Axiom InterpUnivN_Sig_inv_nopf : forall Ξ i ℓ0 A B P,
    ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ P ->
    exists (PA : T -> tm -> Prop),
      ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
      (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = SumSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB).

  Axiom InterpUnivN_deterministic : forall Ξ i A PA PB,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> ⟦ Ξ ⊨ A ⟧ i ↘ PB -> PA = PB.

  Axiom InterpUnivN_deterministic' : forall Ξ i j A PA PB,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> ⟦ Ξ ⊨ A ⟧ j ↘ PB -> PA = PB.

  Axiom InterpUniv_Ok : forall Ξ i A PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> forall ℓ a, PA ℓ a -> IOk Ξ ℓ a.

  Axiom adequacy : forall Ξ i A PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> CR Ξ PA /\ wn A.

  Axiom InterpUnivN_WNe : forall Ξ i A,
    wne A -> ⟦ Ξ ⊨ A ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).

  Axiom InterpUnivN_IEq : forall Ξ i A PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ B PB, IEq Ξ ℓ A B -> ⟦ Ξ ⊨ B ⟧ i ↘ PB -> PA = PB.

  Axiom InterpUnivN_Conv : forall Ξ i j A B PA PB,
    ⟦ Ξ ⊨ B ⟧ i ↘ PA -> conv Ξ A B -> ⟦ Ξ ⊨ A ⟧ j ↘ PB -> PA = PB.

  Axiom InterpUnivN_back_clos : forall Ξ i A PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ0 a b, IOk Ξ ℓ0 a -> a ⇒ b -> PA ℓ0 b -> PA ℓ0 a.

  Axiom InterpUnivN_back_clos_star : forall Ξ i A PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ0 a b, IOk Ξ ℓ0 a -> a ⇒* b -> PA ℓ0 b -> PA ℓ0 a.

  Axiom InterpUnivN_Eq : forall Ξ i ℓ0 a b,
    wn a -> wn b ->
    ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘
      (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).

End LogRelFacts.

(** ** Implementation of [LogRelFacts] from the abstract [LogRel] interface

    Every fact below is derived using only the introduction rules and
    induction principle of [M : LogRel] — never the inner [InterpExt]
    encoding. *)
Module LogRelFactsImpl (M : LogRel) : LogRelFacts M.
  Import M.

  #[export]Hint Resolve InterpUnivN_Ne InterpUnivN_Nat InterpUnivN_Fun
    InterpUnivN_Univ InterpUnivN_Void InterpUnivN_Eq_nf InterpUnivN_Sig
    InterpUnivN_Step InterpUnivN_Unit : InterpUnivN.

  Lemma InterpUnivN_Fun_nopf Ξ i ℓ0 A B PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ (ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB)).
  Proof. hauto l:on db:InterpUnivN. Qed.

  Lemma InterpUnivN_Sig_nopf Ξ i ℓ0 A B PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ (SumSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB)).
  Proof. hauto l:on db:InterpUnivN. Qed.

  Lemma InterpUnivN_cumulative Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> forall j, i <= j -> ⟦ Ξ ⊨ A ⟧ j ↘ PA.
  Proof.
    move : i A PA. apply : InterpUnivN_ind;
      hauto l:on solve+:(by lia) db:InterpUnivN.
  Qed.

  Lemma InterpUnivN_preservation Ξ i A B P :
    ⟦ Ξ ⊨ A ⟧ i ↘ P -> A ⇒ B -> ⟦ Ξ ⊨ B ⟧ i ↘ P.
  Proof.
    move => h. move : i A P h B.
    apply : InterpUnivN_ind.
    - hauto lq:on db:InterpUnivN, nfne.
    - hauto lq:on inv:Par db:InterpUnivN.
    - move => i ℓ0 A B PA PF hA ihA hTot hRes ihRes T hT.
      elim /Par_inv : hT => //.
      move => hPar ℓ1 A0 A1 B0 B1 h0 h1 [? ? ?] ?; subst.
      apply : InterpUnivN_Fun; eauto.
      move => a PB ha hPB0.
      apply : ihRes; eauto.
      sfirstorder use:Par_cong, Par_refl.
    - hauto lq:on inv:Par db:InterpUnivN.
    - hauto lq:on inv:Par db:InterpUnivN.
    - move => i ℓ0 a b ha hb T.
      elim /Par_inv => // _ ℓ1 ? ? a0 b0 ? ? [*]. subst.
      have heq : (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p))
               = (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a0 b0) \/ wne p)).
      { fext => ℓ p. apply propositional_extensionality.
        suff : IOk Ξ ℓ p -> (iconv Ξ ℓ0 a b <-> iconv Ξ ℓ0 a0 b0) by tauto.
        move => _.
        split.
        + hauto lq:on use:iconv_par2.
        + hauto q:on ctrs:rtc unfold:iconv. }
      rewrite heq.
      apply : InterpUnivN_Eq_nf; eauto with nfne.
    - move => i ℓ0 A B PA PF hA ihA hTot hRes ihRes T hT.
      elim /Par_inv : hT => //.
      move => hPar ℓ1 A0 A1 B0 B1 h0 h1 [? ? ?] ?; subst.
      apply : InterpUnivN_Sig; eauto.
      move => a PB ha hPB0.
      apply : ihRes; eauto.
      sfirstorder use:Par_cong, Par_refl.
    - move => i A A0 PA hAA0 hA0 ihA0 C hAC.
      have [D [h2 h3]] := Par_confluent _ _ _ hAA0 hAC.
      eauto using InterpUnivN_Step.
    - hauto lq:on inv:Par db:InterpUnivN.
  Qed.

  Lemma InterpUnivN_preservation_star Ξ i A B P :
    ⟦ Ξ ⊨ A ⟧ i ↘ P -> A ⇒* B -> ⟦ Ξ ⊨ B ⟧ i ↘ P.
  Proof. move => h hr. elim : A B / hr h; eauto using InterpUnivN_preservation. Qed.

  Lemma InterpUnivN_back_preservation_star Ξ i A B P :
    ⟦ Ξ ⊨ B ⟧ i ↘ P -> A ⇒* B -> ⟦ Ξ ⊨ A ⟧ i ↘ P.
  Proof. move => h hr. move : h. elim : A B / hr; eauto using InterpUnivN_Step. Qed.

  Lemma InterpUnivN_subsumption Ξ i A P :
    ⟦ Ξ ⊨ A ⟧ i ↘ P ->
    forall ℓ ℓ0 a, ℓ ⊆ ℓ0 -> P ℓ a -> P ℓ0 a.
  Proof.
    move : i A P. apply : InterpUnivN_ind;
      hauto lq:on use:ifacts.iok_subsumption unfold:ProdSpace, SumSpace.
  Qed.

  Lemma InterpUnivN_Ne_inv Ξ i A P :
    ne A ->
    ⟦ Ξ ⊨ A ⟧ i ↘ P ->
    P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
  Proof.
    move => hne h. move : hne. move : i A P h. apply : InterpUnivN_ind;
      hauto l:on inv:- db:nfne.
  Qed.

  Lemma InterpUnivN_Nat_inv Ξ i P :
    ⟦ Ξ ⊨ tNat ⟧ i ↘ P ->
    P = fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v.
  Proof.
    move E : tNat => A h. move : E. move : i A P h. apply : InterpUnivN_ind;
      hauto q:on inv:tm,Par.
  Qed.

  Lemma InterpUnivN_Eq_inv Ξ i ℓ0 a b P :
    ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘ P ->
    P = (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).
  Proof.
    move E : (tEq ℓ0 a b) => T h. move : ℓ0 a b E.
    move : i T P h. apply : InterpUnivN_ind.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm,Par.
    - hauto q:on inv:tm,Par.
    - hauto q:on inv:tm,Par.
    - hauto q:on inv:tm,Par.
    - hauto lq:on.
    - hauto q:on inv:tm,Par.
    - move => i A A0 PA hAA0 hA0 ihA0 ℓ0 a b ?. subst.
      elim /Par_inv : hAA0 => // _ ? ? ? a0 b0 ? ? [*]. subst.
      specialize ihA0 with (1 := eq_refl). subst.
      fext => ℓ p. apply propositional_extensionality.
      split.
      + hauto q:on ctrs:rtc unfold:iconv.
      + hauto lq:on use:iconv_par2.
    - hauto q:on inv:tm,Par.
  Qed.

  Lemma InterpUnivN_Void_inv Ξ i P :
    ⟦ Ξ ⊨ tVoid ⟧ i ↘ P -> P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
  Proof.
    move E : tVoid => A h. move : E. move : i A P h. apply : InterpUnivN_ind;
      hauto q:on rew:off inv:Par,tm.
  Qed.

  Lemma InterpUnivN_Unit_inv Ξ i P :
    ⟦ Ξ ⊨ tUnit ⟧ i ↘ P ->
    P = fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (v = tTT \/ ne v).
  Proof.
    move E : tUnit => A h. move : E. move : i A P h. apply : InterpUnivN_ind;
      hauto q:on inv:tm,Par.
  Qed.

  Lemma InterpUnivN_Univ_inv Ξ i j P :
    ⟦ Ξ ⊨ tUniv j ⟧ i ↘ P ->
    P = (fun ℓ0 A => IOk Ξ ℓ0 A /\ exists PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA) /\ j < i.
  Proof.
    move E : (tUniv j) => A h. move : j E. move : i A P h. apply : InterpUnivN_ind;
      hauto q:on rew:off inv:Par,tm.
  Qed.

  (* Private helper: full inversion for tPi (with PF). *)
  Lemma InterpUnivN_Fun_inv Ξ i ℓ0 A B P :
    ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ P ->
    exists (PA : T -> tm -> Prop) (PF : tm -> (T -> tm -> Prop) -> Prop),
      ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
      (forall a, PA ℓ0 a -> exists PB, PF a PB) /\
      (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = ProdSpace Ξ ℓ0 PA PF.
  Proof.
    move E : (tPi ℓ0 A B) => T h. move : ℓ0 A B E.
    move : i T P h. apply : InterpUnivN_ind.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto l:on.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - move => *. subst.
      hauto lq:on rew:off inv:Par use:Par_subst, InterpUnivN_Step.
    - hauto q:on inv:tm.
  Qed.

  (* Private helper: full inversion for tSig (with PF). *)
  Lemma InterpUnivN_Sig_inv Ξ i ℓ0 A B P :
    ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ P ->
    exists PA PF,
      ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
      (forall a, PA ℓ0 a -> exists PB, PF a PB) /\
      (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = SumSpace Ξ ℓ0 PA PF.
  Proof.
    move E : (tSig ℓ0 A B) => T h. move : ℓ0 A B E.
    move : i T P h. apply : InterpUnivN_ind.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto q:on inv:tm.
    - hauto l:on.
    - move => *. subst.
      hauto lq:on inv:Par use:Par_subst, InterpUnivN_Step.
    - hauto q:on inv:tm.
  Qed.

  Lemma InterpUnivN_deterministic Ξ i A PA PB :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> ⟦ Ξ ⊨ A ⟧ i ↘ PB -> PA = PB.
  Proof.
    move => h. move : PB.
    move : i A PA h. apply : InterpUnivN_ind.
    - hauto lq:on use:InterpUnivN_Ne_inv.
    - hauto lq:on use:InterpUnivN_Nat_inv.
    - move => i ℓ0 A B PA PF hA ihA hTot hRes ihRes P hP.
      move /InterpUnivN_Fun_inv : hP.
      intros (PA0 & PF0 & hPA0 & hPF0Tot & hPF0 & ?); subst.
      have ? : PA0 = PA by sfirstorder. subst.
      rewrite /ProdSpace.
      fext => *.
      apply propositional_extensionality.
      hauto lq:on rew:off.
    - hauto lq:on use:InterpUnivN_Univ_inv.
    - hauto lq:on use:InterpUnivN_Void_inv.
    - hauto lq:on use:InterpUnivN_Eq_inv.
    - move => i ℓ0 A B PA PF hA ihA hTot hRes ihRes P hP.
      move /InterpUnivN_Sig_inv : hP.
      intros (PA0 & PF0 & hPA0 & hPF0Tot & hPF0 & ?); subst.
      have ? : PA0 = PA by sfirstorder. subst.
      rewrite /SumSpace.
      fext => ℓ t.
      apply propositional_extensionality.
      hauto lq:on rew:off.
    - hauto l:on use:InterpUnivN_preservation.
    - hauto lq:on use:InterpUnivN_Unit_inv.
  Qed.

  Lemma InterpUnivN_Fun_inv_nopf Ξ i ℓ0 A B P :
    ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ P ->
    exists PA,
      ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
      (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB).
  Proof.
    move /InterpUnivN_Fun_inv. intros (PA & PF & hPA & hPF & hPF' & ?); subst.
    exists PA. repeat split => //.
    - sfirstorder.
    - fext => b a.
      apply propositional_extensionality.
      rewrite /ProdSpace.
      have : forall (A B C : Prop), (B <-> C) -> (A /\ B <-> A /\ C) by tauto.
      apply.
      split.
      + move => h a0 PB /[dup] ?.
        move : hPF. move /[apply]. intros (PB0 & hPB0). move => *.
        have ? : PB0 = PB by eauto using InterpUnivN_deterministic.
        sfirstorder.
      + sfirstorder.
  Qed.

  Lemma InterpUnivN_Sig_inv_nopf Ξ i ℓ0 A B P :
    ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ P ->
    exists (PA : T -> tm -> Prop),
      ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
      (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = SumSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB).
  Proof.
    move /InterpUnivN_Sig_inv. intros (PA & PF & hPA & hPF & hPF' & ?); subst.
    exists PA. repeat split => //.
    - sfirstorder.
    - fext => ℓ b.
      rewrite /SumSpace.
      do 2 f_equal.
      apply propositional_extensionality.
      split.
      + move => [a][b0][h0][+]h1.
        move/[dup] => ? /hPF.
        move => [PB]hPB.
        exists a, b0. (repeat split)=>// PB0 ?.
        suff : PB0 = PB by hauto lq:on.
        eauto using InterpUnivN_deterministic.
      + sfirstorder.
  Qed.

  Lemma InterpUnivN_deterministic' Ξ i j A PA PB :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> ⟦ Ξ ⊨ A ⟧ j ↘ PB -> PA = PB.
  Proof.
    move => h0 h1.
    have : i <= max i j by lia.
    have : j <= max i j by lia.
    move /(InterpUnivN_cumulative _ _ _ _ h1) => h1'.
    move /(InterpUnivN_cumulative _ _ _ _ h0) => h0'.
    eauto using InterpUnivN_deterministic.
  Qed.

  Lemma InterpUniv_Ok Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> forall ℓ a, PA ℓ a -> IOk Ξ ℓ a.
  Proof.
    move : i A PA. apply : InterpUnivN_ind;
      hauto lq:on unfold:ProdSpace, SumSpace.
  Qed.

  Lemma InterpUnivN_WNe Ξ i A :
    wne A -> ⟦ Ξ ⊨ A ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).
  Proof.
    rewrite {1}/wne. move => [A0 [h]].
    elim : A A0 / h.
    - apply InterpUnivN_Ne.
    - hauto lq:on use:InterpUnivN_Step.
  Qed.

  Lemma adequacy Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA -> CR Ξ PA /\ wn A.
  Proof.
    set tD := tAbsurd tVoid.
    have tDne : wne tD /\ forall Ξ' ℓ, IOk Ξ' ℓ tD by hauto lq:on ctrs:rtc, IOk.
    move : i A PA. apply : InterpUnivN_ind; rewrite /CR.
    - firstorder with nfne.
    - firstorder with nfne.
    - move => i ℓ0 A B PA PF hPA ihPA hTot hRes ihRes.
      have hzero : PA ℓ0 tD by hauto l:on use:wne_var.
      split.
      split.
      + rewrite /ProdSpace => ℓ b [hb' hb].
        move /hTot : (hzero) => [PB] hPB.
        move /ihRes : (hzero) (hPB) => /[apply].
        move => [ih0][vB]ih2.
        apply : ext_wn. hauto lq:on.
      + rewrite /ProdSpace => ℓ b hb hb'.
        split => //.
        move => a PB ha.
        have wna : wn a by hauto l:on.
        hauto lq:on ctrs:IOk use:wne_app, InterpUniv_Ok.
      + apply wn_pi.
        sfirstorder.
        move /hTot : (hzero) => [PB] hPB.
        move /ihRes : (hzero) hPB => /[apply].
        move => [[_ _]h].
        apply wn_antirenaming with (ξ := (tD..))=>//.
        case => //=.
    - move => i j hji ih.
      split.
      split.
      + move => ℓ A [_ [PA hPA]]. by case : (ih A PA hPA) => _.
      + move => ℓ A hwne hOk. split=>//. exists (fun ℓ a => IOk Ξ ℓ a /\ wne a).
        by apply InterpUnivN_WNe.
      + hauto lq:on db:nfne.
    - hauto lq:on db:nfne.
    - qauto l:on use:wn_eq ctrs:rtc db:nfne.
    - move => i ℓ0 A B PA PF hPA ihPA hTot hRes ihRes.
      rewrite /SumSpace.
      repeat split=>//.
      + move => ℓ t [?][];
               last by apply wne_wn.
        move => [a][b][h0 [h1 h2]].
        rewrite /wn.
        suff : wn (tPack ℓ0 a b) by qauto l:on use:rtc_transitive.
        have : wn b by qauto l:on.
        have : wn a by sfirstorder.
        apply wn_pack.
      + tauto.
      + apply wn_sig.
        sfirstorder.
        have : PA ℓ0 tD by hauto l:on use:wne_var.
        move /[dup] /hTot => [PB] hPB.
        move /ihRes : (hPB) => /[apply].
        move => [_].
        move /wn_antirenaming.
        apply.
        case => //=.
    - hauto lq:on ctrs:rtc.
    - hauto q:on ctrs:rtc db:nfne.
  Qed.

  (* Private helper: Ne_inv generalised to IEq-related terms. *)
  Lemma InterpUnivN_Ne_inv' Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ B, ne B -> IEq Ξ ℓ B A -> PA = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
  Proof.
    move : i A PA. apply : InterpUnivN_ind.
    - sfirstorder.
    - hauto q:on inv:IEq.
    - hauto q:on inv:IEq.
    - hauto q:on inv:IEq.
    - hauto q:on inv:IEq.
    - hauto q:on inv:IEq.
    - hauto q:on inv:IEq.
    - move => i A A0 PA hr hPA ih ℓ B hB hBA.
      move /ifacts.ieq_sym in hBA.
      move : (proj1 (simulation Ξ ℓ)) hBA (hr). repeat move/[apply].
      move => [B0][hr']hBA.
      have : ne B0 by hauto lb:on use:nf_ne_preservation.
      by move /ifacts.ieq_sym /ih : hBA.
    - hauto lq:on inv:IEq.
  Qed.

  Lemma InterpUnivN_IEq Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ B PB, IEq Ξ ℓ A B -> ⟦ Ξ ⊨ B ⟧ i ↘ PB -> PA = PB.
  Proof.
    move : i A PA. apply : InterpUnivN_ind.
    - hauto lq:on use:InterpUnivN_Ne_inv'.
    - hauto q:on inv:IEq use:InterpUnivN_Nat_inv.
    - move => i ℓ0 A B PA PF hPA ihPA hTot hRes ihRes ℓ1 T PB.
      elim /IEq_inv=>// _ ? A0 A1 B0 B1 h0 h1 [? ? ?] ?. subst.
      move /InterpUnivN_Fun_inv_nopf.
      move => [PA0][hPA0][hPB0]?. subst.
      rewrite /ProdSpace.
      fext => ℓ b. f_equal.
      fext => a PB. apply propositional_extensionality.
      have ? : PA0 = PA by sfirstorder. subst.
      have : forall (P Q R: Prop), (P -> (Q <-> R)) -> ((P -> Q) <-> (P -> R)) by tauto.
      apply => ha.
      have ha' : IOk Ξ ℓ0 a by sfirstorder use:InterpUniv_Ok.
      have hB : IEq Ξ ℓ1 B[a..] B1[a..] by eauto using ifacts.ieq_iok_subst.
      split.
      + move => *.
        move /hTot : (ha).
        hauto l:on.
      + hauto lq:on rew:off.
    - hauto lq:on inv:IEq use:InterpUnivN_Univ_inv.
    - hauto lq:on inv:IEq use:InterpUnivN_Void_inv.
    - move => i ℓ0 a b ha hb ℓ B PB.
      elim /IEq_inv=>//= _ ? ? a0 ? b0  ? ha0 hb0 [? ? ?] ?. subst.
      move /InterpUnivN_Eq_inv => ?. subst.
      fext => ℓ1 p. f_equal. apply propositional_extensionality.
      suff : iconv Ξ ℓ0 a b <-> iconv Ξ ℓ0 a0 b0 by tauto.
      apply ieq_iconv in ha0, hb0.
      hauto lq:on rew:off use:iconv_trans_heterogeneous_leq, iconv_trans_heterogeneous_leq', iconv_sym.
    - move => i ℓ0 A B PA PF hPA ihPA hTot hRes ihRes ℓ1 T PB.
      elim /IEq_inv=>// _ ? A0 A1 B0 B1 h0 h1 [? ? ?] ?. subst.
      move /InterpUnivN_Sig_inv_nopf.
      move => [PA0][hPA0][hPB0]?. subst.
      rewrite /SumSpace.
      fext => ℓ b. do 2 f_equal.
      apply propositional_extensionality.
      have ? : PA0 = PA by sfirstorder. subst.
      hauto lq:on rew:off use:InterpUniv_Ok, ifacts.ieq_iok_subst.
    - hauto lq:on rew:off use:simulation, InterpUnivN_preservation.
    - hauto lq:on inv:IEq use:InterpUnivN_Unit_inv.
  Qed.

  Lemma InterpUnivN_Conv Ξ i j A B PA PB :
    ⟦ Ξ ⊨ B ⟧ i ↘ PA -> conv Ξ A B -> ⟦ Ξ ⊨ A ⟧ j ↘ PB -> PA = PB.
  Proof.
    rewrite /conv. move => + [ℓ][c0][c1][h0][h1]h2 + .
    move => hPA hPB.
    have ? : ⟦ Ξ ⊨ c1 ⟧ i ↘ PA by eauto using InterpUnivN_preservation_star.
    have ? : ⟦ Ξ ⊨ c0 ⟧ j ↘ PB by eauto using InterpUnivN_preservation_star.
    have : ⟦ Ξ ⊨ c1 ⟧ (max i j) ↘ PA by
      hauto q:on use:InterpUnivN_cumulative solve+:lia.
    have : ⟦ Ξ ⊨ c0 ⟧ (max i j) ↘ PB by
      hauto q:on use:InterpUnivN_cumulative solve+:lia.
    hauto lq:on use:InterpUnivN_IEq.
  Qed.

  Lemma InterpUnivN_back_clos Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ0 a b, IOk Ξ ℓ0 a -> a ⇒ b -> PA ℓ0 b -> PA ℓ0 a.
  Proof.
    move : i A PA. apply : InterpUnivN_ind.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc.
    - have ? : forall ℓ0 b0 b1 a, b0 ⇒ b1 -> tApp b0 ℓ0 a ⇒ tApp b1 ℓ0 a
        by hauto lq:on ctrs:Par use:Par_refl.
      hauto l:on ctrs:IOk use:InterpUniv_Ok unfold:ProdSpace.
    - move => i j hji ih ℓ0 a b ha hr [hOk_b [PA hPA]].
      split=>//. exists PA. by apply : InterpUnivN_Step; eauto.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc.
    - hauto lq:on ctrs:rtc unfold:SumSpace.
    - sfirstorder.
    - hauto lq:on ctrs:rtc.
  Qed.

  Lemma InterpUnivN_back_clos_star Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ0 a b, IOk Ξ ℓ0 a -> a ⇒* b -> PA ℓ0 b -> PA ℓ0 a.
  Proof.
    move => h ℓ0 a b /[swap].
    induction 1. sfirstorder use:InterpUnivN_back_clos.
    hauto lq:on use:iok_preservation, InterpUnivN_back_clos.
  Qed.

  Lemma InterpUnivN_Eq Ξ i ℓ0 a b :
    wn a -> wn b ->
    ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘
      (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).
  Proof.
    move => [va [? ?]] [vb [? ?]].
    have ? : ⟦ Ξ ⊨ tEq ℓ0 va vb ⟧ i ↘
              (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 va vb) \/ wne p))
      by apply InterpUnivN_Eq_nf.
    have ? : (tEq ℓ0 a b) ⇒* (tEq ℓ0 va vb) by auto using S_Eq.
    have : ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘
            (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 va vb) \/ wne p))
      by eauto using InterpUnivN_back_preservation_star.
    move /[dup] /InterpUnivN_Eq_inv. congruence.
  Qed.

End LogRelFactsImpl.

(** ** Concrete implementation of [LogRel]

    We define the inner inductive [InterpExt] and tie the knot using
    Equations. The [LogRel] interface is then satisfied by deriving each
    introduction rule and the custom induction principle. *)
Module LogRelImpl <: LogRel.

  (* Fig. 12 (Definition of the logical predicate) *)
  Reserved Notation " ⟦ Ξ ⊨ A ⟧ i ; I ↘ S" (at level 70, no associativity).
  Inductive InterpExt Ξ i (I : nat -> tm -> Prop) : tm -> (T -> tm -> Prop) -> Prop :=
  | InterpExt_Ne A : ne A -> ⟦ Ξ ⊨ A ⟧ i ; I ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a)
  | InterpExt_Nat : ⟦ Ξ ⊨ tNat ⟧ i ; I ↘ (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v)
  | InterpExt_Fun ℓ0 A B PA PF :
    InterpExt Ξ i I A PA ->
    (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
    (forall a PB, PA ℓ0 a -> PF a PB -> InterpExt Ξ i I B[a..] PB) ->
    InterpExt Ξ i I (tPi ℓ0 A B) (ProdSpace Ξ ℓ0 PA PF)
  | InterpExt_Univ j :
    j < i ->
    InterpExt Ξ i I (tUniv j) (fun ℓ A => IOk Ξ ℓ A /\  I j A)
  | InterpExt_Void :
    InterpExt Ξ i I tVoid (fun ℓ a => IOk Ξ ℓ a /\ wne a)
  | InterpExt_Eq ℓ0 a b :
    nf a ->
    nf b ->
    InterpExt Ξ i I (tEq ℓ0 a b) (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p))
  | InterpExt_Sig ℓ0 A B PA PF :
    InterpExt Ξ i I A PA ->
    (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
    (forall a PB, PA ℓ0 a -> PF a PB -> InterpExt Ξ i I B[a..] PB) ->
    InterpExt Ξ i I (tSig ℓ0 A B) (SumSpace Ξ ℓ0 PA PF)
  | InterpExt_Step A A0 PA :
    (A ⇒ A0) ->
    InterpExt Ξ i I A0 PA ->
    InterpExt Ξ i I A PA
  | InterpExt_Unit : ⟦ Ξ ⊨ tUnit ⟧ i ; I ↘ (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (v = tTT \/ ne v))
  where " ⟦ Ξ ⊨ A ⟧ i ; I ↘ S" := (InterpExt Ξ i I A S).

  Lemma InterpExt_Eq' Ξ i I ℓ0 a b P :
    nf a ->
    nf b ->
    P = (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)) ->
    InterpExt Ξ i I (tEq ℓ0 a b) P.
  Proof. hauto lq:on use:InterpExt_Eq. Qed.

  Equations InterpUnivN (Ξ : econtext) (n : nat) : tm -> (T -> tm -> Prop) -> Prop
    by wf n lt :=
    InterpUnivN Ξ n := InterpExt Ξ n
                         (fun m A =>
                            match Compare_dec.lt_dec m n with
                            | left h => exists PA, InterpUnivN Ξ m A PA
                            | right _ => False
                            end).

  Notation " ⟦ Ξ ⊨ A ⟧ i  ↘ S" := (InterpUnivN Ξ i A S)
                                    (at level 70, no associativity).

  Lemma InterpExt_Univ' i Ξ I j PF :
    PF = (fun ℓ A => IOk Ξ ℓ A /\  I j A) ->
    j < i ->
    InterpExt Ξ i I (tUniv j) PF.
  Proof. hauto lq:on ctrs:InterpExt. Qed.

  (* The definition of InterpUnivN is more complicated than
     it needs to be. We show that we can simplify the unfolding
     above to just mention InterpUnivN without doing the case analysis. *)
  Lemma InterpExt_lt_redundant i Ξ I A PA
    (h : ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA) :
       ⟦ Ξ ⊨ A ⟧ i ; (fun j A =>
                       match Compare_dec.lt_dec j i with
                       | left h => I j A
                       | right _ => False
                       end) ↘ PA.
  Proof.
    elim : A PA / h.
    - hauto lq:on ctrs:InterpExt.
    - hauto l:on.
    - hauto l:on ctrs:InterpExt.
    - move => m h.
      apply InterpExt_Univ' => //.
      case : Compare_dec.lt_dec => //.
    - hauto l:on ctrs:InterpExt.
    - hauto l:on ctrs:InterpExt.
    - hauto l:on ctrs:InterpExt.
    - hauto l:on ctrs:InterpExt.
    - hauto l:on ctrs:InterpExt.
  Qed.

  Lemma InterpExt_lt_redundant2 Ξ i I A PA
    (h : ⟦ Ξ ⊨ A ⟧ i ; (fun j A =>
                         match Compare_dec.lt_dec j i with
                        | left h => I j A
                        | right _ => False
                        end) ↘ PA) :
    ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA.
  Proof.
    elim : A PA / h.
    - hauto lq:on ctrs:InterpExt.
    - hauto l:on.
    - hauto l:on ctrs:InterpExt.
    - move => m ?.
      apply InterpExt_Univ' => //.
      case : Compare_dec.lt_dec => //.
    - hauto l:on ctrs:InterpExt.
    - hauto l:on ctrs:InterpExt.
    - hauto lq:on ctrs:InterpExt.
    - hauto l:on ctrs:InterpExt.
    - hauto l:on ctrs:InterpExt.
  Qed.

  Lemma InterpUnivN_nolt Ξ i :
    InterpUnivN Ξ i = InterpExt Ξ i (fun j A => exists PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA).
  Proof.
    simp InterpUnivN.
    fext => A P.
    apply propositional_extensionality.
    hauto l:on use:InterpExt_lt_redundant, InterpExt_lt_redundant2.
  Qed.

  #[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

  (** *** Introduction rules satisfying the [LogRel] interface *)

  Lemma InterpUnivN_Ne Ξ i A :
    ne A ->
    ⟦ Ξ ⊨ A ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).
  Proof. simp InterpUnivN. apply InterpExt_Ne. Qed.

  Lemma InterpUnivN_Nat Ξ i :
    ⟦ Ξ ⊨ tNat ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v).
  Proof. simp InterpUnivN. apply InterpExt_Nat. Qed.

  Lemma InterpUnivN_Fun Ξ i ℓ0 A B PA PF :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
    (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ ProdSpace Ξ ℓ0 PA PF.
  Proof. hauto l:on ctrs:InterpExt rew:db:InterpUniv. Qed.

  Lemma InterpUnivN_Univ Ξ i j :
    j < i ->
    ⟦ Ξ ⊨ tUniv j ⟧ i ↘ (fun ℓ A => IOk Ξ ℓ A /\ exists PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA).
  Proof.
    move => hji.
    simp InterpUniv.
    apply InterpExt_Univ' => [|//].
    by simp InterpUniv.
  Qed.

  Lemma InterpUnivN_Void Ξ i :
    ⟦ Ξ ⊨ tVoid ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).
  Proof. simp InterpUnivN. apply InterpExt_Void. Qed.

  Lemma InterpUnivN_Eq_nf Ξ i ℓ0 a b :
    nf a -> nf b ->
    ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘
      (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).
  Proof. simp InterpUnivN. apply InterpExt_Eq. Qed.

  Lemma InterpUnivN_Sig Ξ i ℓ0 A B PA PF :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
    (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
    ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ SumSpace Ξ ℓ0 PA PF.
  Proof. hauto l:on ctrs:InterpExt rew:db:InterpUniv. Qed.

  Lemma InterpUnivN_Step Ξ i A A0 PA :
    A ⇒ A0 -> ⟦ Ξ ⊨ A0 ⟧ i ↘ PA -> ⟦ Ξ ⊨ A ⟧ i ↘ PA.
  Proof. hauto l:on ctrs:InterpExt rew:db:InterpUniv. Qed.

  Lemma InterpUnivN_Unit Ξ i :
    ⟦ Ξ ⊨ tUnit ⟧ i ↘
      (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (v = tTT \/ ne v)).
  Proof. simp InterpUnivN. apply InterpExt_Unit. Qed.

  Lemma InterpUnivN_ind Ξ (P : nat -> tm -> (T -> tm -> Prop) -> Prop) :
    (forall i A, ne A ->
       P i A (fun ℓ a => IOk Ξ ℓ a /\ wne a)) ->
    (forall i,
       P i tNat (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v)) ->
    (forall i ℓ0 A B PA PF,
       ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
       P i A PA ->
       (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> P i B[a..] PB) ->
       P i (tPi ℓ0 A B) (ProdSpace Ξ ℓ0 PA PF)) ->
    (forall i j, j < i ->
       (forall A PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA -> P j A PA) ->
       P i (tUniv j) (fun ℓ A => IOk Ξ ℓ A /\ exists PA, ⟦ Ξ ⊨ A ⟧ j ↘ PA)) ->
    (forall i,
       P i tVoid (fun ℓ a => IOk Ξ ℓ a /\ wne a)) ->
    (forall i ℓ0 a b, nf a -> nf b ->
       P i (tEq ℓ0 a b)
         (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p))) ->
    (forall i ℓ0 A B PA PF,
       ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
       P i A PA ->
       (forall a, PA ℓ0 a -> exists PB, PF a PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
       (forall a PB, PA ℓ0 a -> PF a PB -> P i B[a..] PB) ->
       P i (tSig ℓ0 A B) (SumSpace Ξ ℓ0 PA PF)) ->
    (forall i A A0 PA,
       A ⇒ A0 -> ⟦ Ξ ⊨ A0 ⟧ i ↘ PA -> P i A0 PA -> P i A PA) ->
    (forall i,
       P i tUnit (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (v = tTT \/ ne v))) ->
    forall i A PA, ⟦ Ξ ⊨ A ⟧ i ↘ PA -> P i A PA.
  Proof.
    move => hNe hNat hFun hUniv hVoid hEq hSig hStep hUnit.
    move => i A PA h.
    move : A PA h.
    elim /Wf_nat.lt_wf_ind : i => i ih A PA.
    simp InterpUniv.
    move => h.
    elim : A PA / h.
    - eauto.
    - eauto.
    - move => ℓ0 A B PA PF hPA ihPA hTot hRes ihPF.
      apply hFun => //.
      + by simp InterpUniv.
      + move => a PB ha hPB. by simp InterpUniv; apply hRes.
    - move => j hj.
      apply hUniv => //.
      move => A PA hPA. by apply ih.
    - eauto.
    - eauto.
    - move => ℓ0 A B PA PF hPA ihPA hTot hRes ihPF.
      apply hSig => //.
      + by simp InterpUniv.
      + move => a PB ha hPB. by simp InterpUniv; apply hRes.
    - move => A A0 PA hAA0 hA0 ihA0.
      apply hStep with (A0 := A0) => //.
      by simp InterpUniv.
    - eauto.
  Qed.

End LogRelImpl.

(** ** Tie facts to the concrete impl *)
Module LRFacts := LogRelFactsImpl LogRelImpl.

(** Expose names from both modules to lr_sig for downstream consumers. *)
Include LogRelImpl.
Include LRFacts.

End lr_sig.
