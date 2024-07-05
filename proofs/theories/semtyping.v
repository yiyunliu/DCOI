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

Definition ProdSpace Ξ ℓ0 (PA : T -> tm -> Prop) (PF : tm -> (T -> tm -> Prop) -> Prop)ℓ (b : tm) :=
  IOk Ξ ℓ b /\
  forall a PB, PA ℓ0 a -> PF a PB -> PB ℓ (tApp b ℓ0 a).

Definition SumSpace Ξ ℓ0 (PA : T -> tm -> Prop) (PF : tm -> (T -> tm -> Prop) -> Prop)ℓ (t : tm) :=
  IOk Ξ ℓ t /\
  ((exists a b, t ⇒* tPack ℓ0 a b /\ PA ℓ0 a /\ (forall PB, PF a PB -> PB ℓ b)) \/ wne t).

(* Logical Relation:

  InterpUnivN i A P  holds when
   - A is a Set i
   - P is a predicate on terms that act like type A

  We define this in two parts: one that generalizes over
  smaller interpretations and then tie the knot
  with the real definition below.

 *)


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

(* ---------------------------------------------------- *)

(* The definition of InterpUnivN is more complicated than
   it needs to be. We show that that we can
   simplify the unfolding above to just mention InterpUnivN
   without doing the case analysis.
*)
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

Lemma InterpExt_Fun_inv Ξ i I ℓ0 A B P
  (h :  ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ; I ↘ P) :
  exists (PA : T -> tm -> Prop) (PF : tm -> (T -> tm -> Prop) -> Prop),
     ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA /\
    (forall a, PA ℓ0 a -> exists PB, PF a PB) /\
    (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB) /\
    P = ProdSpace Ξ ℓ0 PA PF.
Proof.
  move E : (tPi ℓ0 A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - hauto q:on inv:tm.
  - hauto l:on.
  - move => *. subst.
    hauto lq:on rew:off inv:Par ctrs:InterpExt use:Par_subst.
Qed.

Lemma InterpExt_Sig_inv Ξ i I ℓ0 A B P
  (h :  ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ; I ↘ P) :
  exists PA PF,
     ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA /\
    (forall a, PA ℓ0 a -> exists PB, PF a PB) /\
    (forall a PB, PA ℓ0 a -> PF a PB -> ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB) /\
    P = SumSpace Ξ ℓ0 PA PF.
Proof.
  move E : (tSig ℓ0 A B) h => T h.
  move : ℓ0 A B E.
  elim : T P / h => //.
  - hauto q:on inv:tm.
  - hauto l:on.
  - move => *; subst.
    hauto lq:on inv:Par ctrs:InterpExt use:Par_subst.
Qed.

(* For all of the proofs about InterpUnivN below, we need to
   do them in two steps. Once for InterpExt, and then tie the
   knot for the full definition. *)

(* -----  I-PiAlt is admissible (free of PF, the relation R on paper)  ---- *)

Lemma InterpExt_Fun_nopf Ξ i I ℓ0 A B PA :
  ⟦ Ξ ⊨ A ⟧ i ;I ↘ PA ->
  (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB) ->
  ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ; I ↘ (ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB)).
Proof.
  hauto l:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_Fun_nopf Ξ i ℓ0 A B PA :
  ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
  (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
  ⟦ Ξ ⊨ tPi ℓ0 A B ⟧ i ↘ (ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB)).
Proof.
  hauto l:on use:InterpExt_Fun_nopf rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Sig_nopf Ξ i ℓ0 A B PA :
  ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
  (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) ->
  ⟦ Ξ ⊨ tSig ℓ0 A B ⟧ i ↘ (SumSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB)).
Proof.
  hauto l:on ctrs:InterpExt rew:db:InterpUniv.
Qed.

(* --------------- relation is cumulative ----------------- *)

Lemma InterpExt_cumulative Ξ i j I A PA :
  i <= j ->
   ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA ->
   ⟦ Ξ ⊨ A ⟧ j ; I ↘ PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt use:PeanoNat.Nat.le_trans.
Qed.

Lemma InterpUnivN_cumulative Ξ i A PA :
   ⟦ Ξ ⊨ A ⟧ i ↘ PA -> forall j, i <= j ->
   ⟦ Ξ ⊨ A ⟧ j ↘ PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

(* ------------------------------------------------------- *)

(* The logical relation is closed under parallel reduction,
   forwards and backwards. *)

Lemma InterpExt_preservation Ξ i I A B P (h : ⟦ Ξ ⊨ A ⟧ i ; I ↘ P) :
  (A ⇒ B) ->
  ⟦ Ξ ⊨ B ⟧ i ; I ↘ P.
Proof.
  move : B.
  elim : A P / h; auto.
  - hauto lq:on ctrs:InterpExt db:nfne.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - move => ℓ0 A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv :  hT => //.
    move => hPar ℓ1 A0 A1 B0 B1 h0 h1 [? ? ?] ?; subst.
    apply InterpExt_Fun; auto.
    move => a PB ha hPB0.
    apply : ihPB; eauto.
    sfirstorder use:Par_cong, Par_refl.
  - hauto lq:on inv:Par ctrs:InterpExt.
  - inversion 1. sfirstorder.
  - move => ℓ0 a b ? ?  B.
    elim /Par_inv => // _ ℓ1 ? ? a0 b0 ? ?[*]. subst.
    apply InterpExt_Eq'; eauto with nfne.
    fext => ℓ p.
    apply propositional_extensionality.
    suff : IOk Ξ ℓ p -> (iconv Ξ ℓ0 a b <-> iconv Ξ ℓ0 a0 b0) by tauto.
    move => h.
    split.
    + hauto lq:on use:iconv_par2.
    + hauto q:on ctrs:rtc unfold:iconv .
  - move => ℓ0 A B PA PF hPA ihPA hPB hPB' ihPB T hT.
    elim /Par_inv :  hT => //.
    move => hPar ℓ1 A0 A1 B0 B1 h0 h1 [? ? ?] ?; subst.
    apply InterpExt_Sig; auto.
    move => a PB ha hPB0.
    apply : ihPB; eauto.
    sfirstorder use:Par_cong, Par_refl.
  - move => A B P h0 h1 ih1 C hC.
    have [D [h2 h3]] := Par_confluent _ _ _ h0 hC.
    hauto lq:on ctrs:InterpExt.
Qed.

Lemma InterpUnivN_preservation Ξ i A B P (h : ⟦ Ξ ⊨ A ⟧ i ↘ P) :
  (A ⇒ B) ->
  ⟦ Ξ ⊨ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use: InterpExt_preservation. Qed.

Lemma InterpExt_back_preservation_star Ξ i I A B P (h : ⟦ Ξ ⊨ B ⟧ i ; I ↘ P) :
  A ⇒* B ->
  ⟦ Ξ ⊨ A ⟧ i ; I ↘ P.
Proof. induction 1; hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_preservation_star Ξ i I A B P (h : ⟦ Ξ ⊨ A ⟧ i ; I ↘ P) :
  A ⇒* B ->
  ⟦ Ξ ⊨ B ⟧ i ; I ↘ P.
Proof. induction 1; hauto l:on use:InterpExt_preservation. Qed.

Lemma InterpUnivN_preservation_star Ξ i A B P (h : ⟦ Ξ ⊨ A ⟧ i ↘ P) :
  A ⇒* B ->
  ⟦ Ξ ⊨ B ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_preservation_star. Qed.

Lemma InterpUnivN_back_preservation_star Ξ i A B P (h : ⟦ Ξ ⊨ B ⟧ i ↘ P) :
  A ⇒* B ->
  ⟦ Ξ ⊨ A ⟧ i ↘ P.
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_back_preservation_star. Qed.

Lemma InterpExt_subsumption Ξ i I A P (h : ⟦ Ξ ⊨ A ⟧ i ; I ↘ P) :
  forall ℓ ℓ0 a, ℓ ⊆ ℓ0 -> P ℓ a -> P ℓ0 a.
Proof.
  elim : A P / h;
    hauto lq:on use:ifacts.iok_subsumption unfold:ProdSpace.
Qed.

Lemma InterpUnivN_subsumption Ξ i A P : ⟦ Ξ ⊨ A ⟧ i ↘ P ->
  forall ℓ ℓ0 a, ℓ ⊆ ℓ0 -> P ℓ a -> P ℓ0 a.
Proof. simp InterpUnivN. apply InterpExt_subsumption. Qed.

(* ---------------------------------------------------------- *)
(* inversion lemmas for InterpExt. To invert the InterpExt
   judgment, we have to be careful about the step case. *)

Lemma InterpExt_Ne_inv Ξ i I A P :
  ne A ->
  ⟦ Ξ ⊨ A ⟧ i ; I ↘ P ->
  P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
Proof.
  move => + h0.
  elim : A P /h0 =>//.
  hauto l:on inv:- db:nfne.
Qed.

Lemma InterpExt_Nat_inv Ξ i I P :
  ⟦ Ξ ⊨ tNat ⟧ i ; I ↘ P ->
  P = fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v.
Proof.
  move E : tNat => A h.
  move : E.
  elim : A P / h; hauto q:on inv:tm,Par.
Qed.

Lemma InterpExt_Univ_inv Ξ i I P j :
  ⟦ Ξ ⊨ tUniv j ⟧ i ; I ↘ P ->
  P = (fun ℓ A => IOk Ξ ℓ A /\  I j A) /\ j < i.
Proof.
  move E : (tUniv j) => A h.
  move : E.
  elim : A P / h; hauto q:on rew:off inv:Par,tm.
Qed.

Lemma InterpExt_Void_inv Ξ i I P :
  ⟦ Ξ ⊨ tVoid ⟧ i ; I ↘ P ->
  P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
Proof.
  move E : tVoid => A h.
  move : E.
  elim : A P / h; hauto q:on rew:off inv:Par,tm.
Qed.

Lemma InterpExt_Eq_inv Ξ i I ℓ0 a b P :
  ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ; I ↘ P ->
  P = (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).
Proof.
  move E : (tEq ℓ0 a b) => T h.
  move : ℓ0 a b E.
  elim : T P / h=>//.
  - hauto q:on inv:tm.
  - hauto lq:on.
  - move => ? A0 S hA hS ihS ℓ0 a b ?. subst.
    elim /Par_inv : hA=>// _ ? ? ? a0 b0 ? ? [*]. subst.
    specialize ihS with (1 := eq_refl). subst.
    fext => ℓ p. apply propositional_extensionality.
    split.
    + hauto q:on ctrs:rtc unfold:iconv .
    + hauto lq:on use:iconv_par2.
Qed.

Lemma InterpUnivN_Eq_inv Ξ i ℓ0 a b P :
  ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘ P ->
  P = (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).
Proof. simp InterpUniv; apply InterpExt_Eq_inv. Qed.

Lemma InterpUnivN_Void Ξ i :
  ⟦ Ξ ⊨ tVoid ⟧ i ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).
Proof. simp InterpUniv; apply InterpExt_Void. Qed.


Lemma InterpUnivN_Eq Ξ i ℓ0 a b :
  wn a -> wn b ->
  ⟦ Ξ ⊨ tEq ℓ0 a b ⟧ i ↘ (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 a b) \/ wne p)).
Proof.
  move => [va [? ?]] [vb [? ?]].
  have ? : InterpUnivN Ξ i (tEq ℓ0 va vb) (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 va vb) \/ wne p))
    by hauto lq:on ctrs:InterpExt rew:db:InterpUniv.
  have ? : (tEq ℓ0 a b) ⇒* (tEq ℓ0 va vb) by auto using S_Eq.
  have : InterpUnivN Ξ i (tEq ℓ0 a b) (fun ℓ p => IOk Ξ ℓ p /\ ((p ⇒* tRefl /\ iconv Ξ ℓ0 va vb) \/ wne p)) by eauto using InterpUnivN_back_preservation_star.
  move /[dup] /InterpUnivN_Eq_inv. congruence.
Qed.

Lemma InterpUnivN_Void_inv Ξ i P:
  ⟦ Ξ ⊨ tVoid ⟧ i ↘ P -> P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
Proof. simp InterpUniv; apply InterpExt_Void_inv. Qed.

Lemma InterpUnivN_Ne_inv Ξ i A P :
  ne A ->
  ⟦ Ξ ⊨ A ⟧ i ↘ P ->
  P = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
Proof.
  sfirstorder use:InterpExt_Ne_inv rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Nat_inv Ξ i P :
  ⟦ Ξ ⊨ tNat ⟧ i ↘ P ->
  P = fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ (is_nat_val v).
Proof. hauto l:on rew:db:InterpUnivN use:InterpExt_Nat_inv. Qed.

(* ------------- relation is deterministic ---------------- *)

Lemma InterpExt_deterministic Ξ i I A PA PB :
  ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA ->
  ⟦ Ξ ⊨ A ⟧ i ; I ↘ PB ->
  PA = PB.
Proof.
  move => h.
  move : PB.
  elim : A PA / h.
  - hauto lq:on inv:InterpExt ctrs:InterpExt use:InterpExt_Ne_inv.
  - hauto lq:on inv:InterpExt use:InterpExt_Nat_inv.
  - move => ℓ0 A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpExt_Fun_inv : hP.
    intros (PA0 & PF0 & hPA0 & hPB0 & hPB0' & ?); subst.
    have ? : PA0 = PA by sfirstorder. subst.
    rewrite /ProdSpace.
    fext => *.
    apply propositional_extensionality.
    hauto lq:on rew:off.
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Univ_inv.
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Void_inv.
  - hauto lq:on rew:off inv:InterpExt ctrs:InterpExt use:InterpExt_Eq_inv.
  - move => ℓ0 A B PA PF hPA ihPA hPB hPB' ihPB P hP.
    move /InterpExt_Sig_inv : hP.
    intros (PA0 & PF0 & hPA0 & hPB0 & hPB0' & ?); subst.
    have ? : PA0 = PA by sfirstorder. subst.
    rewrite /SumSpace.
    fext => ℓ t.
    apply propositional_extensionality.
    hauto lq:on rew:off.
  - hauto l:on use:InterpExt_preservation.
Qed.

Lemma InterpUnivN_deterministic Ξ i A PA PB :
  ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
  ⟦ Ξ ⊨ A ⟧ i ↘ PB ->
  PA = PB.
Proof.
  simp InterpUnivN. apply InterpExt_deterministic.
Qed.

(* slight generalization to work with any levels using cumulativity. *)


Lemma InterpExt_deterministic' Ξ i j I A PA PB :
   ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA ->
   ⟦ Ξ ⊨ A ⟧ j ; I ↘ PB ->
  PA = PB.
Proof.
  move => h0 h1.
  case : (Coq.Arith.Compare_dec.le_le_S_dec i j).
  - hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
  - move => ?. have : j <= i by lia. hauto l:on use:InterpExt_cumulative, InterpExt_deterministic.
Qed.

Lemma InterpUnivN_deterministic' Ξ i j  A PA PB :
  ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
  ⟦ Ξ ⊨ A ⟧ j ↘ PB ->
  PA = PB.
Proof. hauto lq:on rew:off use:InterpExt_deterministic' rew:db:InterpUniv. Qed.

(* ------ Elements from the interpreted set are all well-graded --- *)
Lemma InterpExt_Ok Ξ i I A PA :
  InterpExt Ξ i I A PA -> forall ℓ a, PA ℓ a -> IOk Ξ ℓ a.
Proof.
  move => h.
  elim : A PA / h.
  - sfirstorder.
  - hauto lq:on.
  - hauto lq:on.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - hauto lq:on.
Qed.

Lemma InterpUniv_Ok Ξ i A PA :
  InterpUnivN Ξ i A PA -> forall ℓ a, PA ℓ a -> IOk Ξ ℓ a.
Proof. simp InterpUniv. apply InterpExt_Ok. Qed.

(* P identifies a set of "reducibility candidates" *)
Definition CR Ξ (P : T -> tm -> Prop) :=
  (forall ℓ a, P ℓ a -> wn a) /\
    (forall ℓ a, wne a -> IOk Ξ ℓ a -> P ℓ a).

Lemma wne_var Ξ ℓ i :
  let tD := tAbsurd (var_tm i) in
  wne tD /\ IOk Ξ ℓ tD.
Proof. hauto lq:on ctrs:rtc, IOk. Qed.

Lemma InterpExt_adequacy Ξ i I A PA
  (hI : forall j A,  j < i -> (I j A -> wn A) /\ (wne A -> I j A))
  (h :  ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA) :
  CR Ξ PA /\ wn A.
Proof.
  set tD := tAbsurd (var_tm 0).
  rewrite /CR.
  elim : A PA / h.
  - firstorder with nfne.
  - firstorder with nfne.
  - move => ℓ0 A B PA PF hPA ihPA hTot hRes ihPF.
    have hzero : PA ℓ0 tD by hauto l:on use:wne_var.
    split.
    split.
    + rewrite /ProdSpace => ℓ b [hb' hb].
      move /hTot : (hzero) => [PB]hPB.
      move /ihPF : (hzero) (hPB) => /[apply].
      move => [ih0][vB]ih2.
      apply : ext_wn. hauto lq:on.
    + rewrite /ProdSpace => ℓ b hb hb'.
      split => //.
      move => a PB ha.
      have wna : wn a by hauto l:on.
      hauto lq:on ctrs:IOk use:wne_app,InterpExt_Ok.
    + apply wn_pi.
      sfirstorder.
      move /hTot : (hzero) => [PB]hPB.
      move /ihPF : (hzero) hPB => /[apply].
      move => [[_ _]h].
      apply wn_antirenaming with (ξ := (tD..))=>//.
      case => //=.
  - hauto l:on.
  - hauto lq:on db:nfne.
  - qauto l:on use:wn_eq ctrs:rtc db:nfne.
  - move => ℓ0 A B PA PF hPA ihPA hTot hRes ihPF.
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
      move /[dup] /hTot => [PB]hPB.
      move /ihPF : (hPB) => /[apply].
      move => [_].
      move /wn_antirenaming.
      apply.
      case => //=.
  - hauto lq:on ctrs:InterpExt, rtc.
Qed.

Lemma InterpUnivN_WNe Ξ i A  : wne A -> ⟦ Ξ ⊨ A ⟧  i  ↘ (fun ℓ a => IOk Ξ ℓ a /\ wne a).
Proof.
  rewrite {1}/wne. move => [A0 [h]].
  elim : A A0 / h.
  - simp InterpUniv. apply InterpExt_Ne.
  - simp InterpUniv. hauto lq:on ctrs:InterpExt.
Qed.


Lemma adequacy Ξ i A PA
  (h :  ⟦ Ξ ⊨ A ⟧ i ↘ PA) :
  CR Ξ PA /\ wn A.
Proof.
  move : i Ξ A PA h.
  elim /Wf_nat.lt_wf_ind => i ih Ξ A PA.
  simp InterpUniv.
  apply InterpExt_adequacy.
  hauto l:on use:InterpUnivN_WNe.
Qed.

Lemma InterpExt_Ne_inv' Ξ i I A PA (h : InterpExt Ξ i I A PA) :
  forall ℓ B, ne B -> IEq Ξ ℓ B A -> PA = (fun ℓ a => IOk Ξ ℓ a /\ wne a).
Proof.
  elim : A PA / h.
  - sfirstorder.
  - hauto q:on inv:IEq.
  - hauto q:on inv:IEq.
  - hauto q:on inv:IEq.
  - hauto q:on inv:IEq.
  - hauto q:on inv:IEq.
  - hauto q:on inv:IEq.
  - move => A A0 PA hr hPA ih ℓ B hB hBA.
    move /ifacts.ieq_sym in hBA.
    move : (proj1 (simulation Ξ ℓ)) hBA (hr). repeat move/[apply].
    move => [B0][hr']hBA.
    have : ne B0 by hauto lb:on use:nf_ne_preservation.
    by move /ifacts.ieq_sym /ih : hBA.
Qed.


Lemma InterpExt_Fun_inv_nopf Ξ i I ℓ0 A B P  (h : InterpExt Ξ i I (tPi ℓ0 A B) P) :
  exists PA,
     ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA /\
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB) /\
      P = ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB).
Proof.
  move /InterpExt_Fun_inv : h. intros (PA & PF & hPA & hPF & hPF' & ?); subst.
  exists PA. repeat split => //.
  - sfirstorder.
  - fext => b a.
    apply propositional_extensionality.
    rewrite /ProdSpace.
    have : forall (A B C : Prop), (B <-> C) -> (A /\ B  <-> A /\ C) by tauto.
    apply.
    split.
    + move => h a0 PB /[dup] ?.
      move : hPF . move /[apply]. intros (PB0 & hPB0). move => *.
      have ? : PB0 = PB by eauto using InterpExt_deterministic.
      sfirstorder.
    + sfirstorder.
Qed.

Lemma InterpExt_Sig_inv_nopf Ξ i I ℓ0 A B P  (h : InterpExt Ξ i I (tSig ℓ0 A B) P) :
  exists (PA : T -> tm -> Prop),
     ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA /\
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB) /\
      P = SumSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ; I ↘ PB).
Proof.
  move /InterpExt_Sig_inv : h. intros (PA & PF & hPA & hPF & hPF' & ?); subst.
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
      eauto using InterpExt_deterministic.
    + sfirstorder.
Qed.


Lemma InterpExt_IEq Ξ i I A PA  (h : InterpExt Ξ i I A PA) :
  forall ℓ B PB, IEq Ξ ℓ A B ->
  InterpExt Ξ i I B PB -> PA = PB.
Proof.
  elim : A PA / h.
  - hauto lq:on use:InterpExt_Ne_inv'.
  - hauto q:on inv:IEq ctrs:InterpExt use:InterpExt_Nat_inv.
  - move => ℓ0 A B PA PF hPA ihPA hTot hRes ihPF ℓ1 T PB.
    elim /IEq_inv=>// _ ? A0 A1 B0 B1 h0 h1 [? ? ?]?. subst.
    move /InterpExt_Fun_inv_nopf.
    move => [PA0][hPA0][hPB0]?. subst.
    rewrite /ProdSpace.
    fext => ℓ b. f_equal.
    fext => a PB. apply propositional_extensionality.
    have ? : PA0 = PA by sfirstorder. subst.
    have : forall (P Q R: Prop), (P -> (Q <-> R))-> ((P -> Q) <-> (P -> R)) by tauto.
    apply => ha.
    have ha' : IOk Ξ ℓ0 a by sfirstorder use:InterpExt_Ok.
    have hB : IEq Ξ ℓ1 B[a..] B1[a..] by eauto using ifacts.ieq_iok_subst.
    split.
    + move => *.
      move /hTot : (ha).
      hauto l:on.
    + hauto lq:on rew:off.
  - hauto lq:on inv:IEq ctrs:InterpExt use:InterpExt_Univ_inv.
  - hauto lq:on inv:IEq ctrs:InterpExt use:InterpExt_Void_inv.
  - move => ℓ0 a b ? ? ℓ B PB.
    elim /IEq_inv=>//= _ ? ? a0 ? b0  ? ha hb [? ? ?] ?. subst.
    move /InterpExt_Eq_inv => ?. subst.
    fext => ℓ1 p. f_equal. apply propositional_extensionality.
    suff : iconv Ξ ℓ0 a b <-> iconv Ξ ℓ0 a0 b0 by tauto.
    apply ieq_iconv in ha, hb.
    hauto lq:on rew:off use:iconv_trans_heterogeneous_leq, iconv_trans_heterogeneous_leq', iconv_sym.
  - move => ℓ0 A B PA PF hPA ihPA hTot hRes ihPF ℓ1 T PB.
    elim /IEq_inv=>// _ ? A0 A1 B0 B1 h0 h1 [? ? ?] ?. subst.
    move /InterpExt_Sig_inv_nopf.
    move => [PA0][hPA0][hPB0]?. subst.
    rewrite /SumSpace.
    fext => ℓ b. do 2 f_equal.
    apply propositional_extensionality.
    have ? : PA0 = PA by sfirstorder. subst.
    hauto lq:on rew:off use:InterpExt_Ok, ifacts.ieq_iok_subst.
  - hauto lq:on rew:off ctrs:InterpExt use:simulation, InterpExt_preservation.
Qed.

Lemma InterpUnivN_IEq Ξ i A PA (h : InterpUnivN Ξ i A PA) :
  forall ℓ B PB, IEq Ξ ℓ A B ->
            InterpUnivN Ξ i B PB ->
            PA = PB.
Proof. hauto q:on use:InterpExt_IEq rew:db:InterpUniv. Qed.

(* ----- Improved inversion lemma for functions (Pi Inv Alt) ---------- *)

(* ---------------------------------------------------------- *)

Lemma InterpUnivN_Conv Ξ i j A B PA PB (h : ⟦ Ξ ⊨ B ⟧ i ↘ PA) :
  conv Ξ A B ->
  ⟦ Ξ ⊨ A ⟧ j ↘ PB -> PA = PB.
Proof.
  rewrite /conv. move => [ℓ][c0][c1][h0][h1]h2 h3.
  have ? : ⟦ Ξ ⊨ c1 ⟧ i ↘ PA by eauto using InterpUnivN_preservation_star.
  have ? : ⟦ Ξ ⊨ c0 ⟧ j ↘ PB by eauto using InterpUnivN_preservation_star.
  have : ⟦ Ξ ⊨ c1 ⟧ (max i j) ↘ PA by
    hauto q:on use:InterpUnivN_cumulative solve+:lia.
  have : ⟦ Ξ ⊨ c0 ⟧ (max i j) ↘ PB by
    hauto q:on use:InterpUnivN_cumulative solve+:lia.
  hauto lq:on use:InterpUnivN_IEq.
Qed.

Lemma InterpUnivN_Fun_inv_nopf Ξ i ℓ0 A B P  (h : InterpUnivN Ξ i (tPi ℓ0 A B) P) :
  exists PA,
    ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = ProdSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB).
Proof.
  qauto use:InterpExt_Fun_inv_nopf l:on rew:db:InterpUniv.
Qed.

Lemma InterpUnivN_Sig_inv_nopf Ξ i ℓ0 A B P  (h : InterpUnivN Ξ i (tSig ℓ0 A B) P) :
  exists (PA : T -> tm -> Prop),
     ⟦ Ξ ⊨ A ⟧ i ↘ PA /\
    (forall a, PA ℓ0 a -> exists PB, ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB) /\
      P = SumSpace Ξ ℓ0 PA (fun a PB => ⟦ Ξ ⊨ B[a..] ⟧ i ↘ PB).
Proof. hauto l:on use:InterpExt_Sig_inv_nopf rew:db:InterpUniv. Qed.

Lemma InterpUnivN_Univ_inv Ξ i j P :
  ⟦ Ξ ⊨ tUniv j ⟧ i ↘ P ->
  P = (fun ℓ0 A => IOk Ξ ℓ0 A /\ exists PA, InterpUnivN Ξ j A PA) /\ j < i.
Proof.
  hauto q:on rew:db:InterpUniv use:InterpExt_Univ_inv.
Qed.

Lemma InterpUnivN_Univ Ξ i j :
  j < i ->
  ⟦ Ξ ⊨ tUniv j ⟧ i ↘  (fun ℓ A => IOk Ξ ℓ A /\ exists PA, InterpUnivN Ξ j A PA).
Proof.
  move => hji.
  simp InterpUniv.
  apply InterpExt_Univ' => [|//].
  by simp InterpUniv.
Qed.

(* Lemma InterpUnivN_WNe i A  : wne A -> ⟦ A ⟧  i  ↘ wne. *)
(* Proof. *)
(*   rewrite {1}/wne. move => [A0 [h]]. *)
(*   elim : A A0 / h. *)
(*   - simp InterpUniv. apply InterpExt_Ne. *)
(*   - simp InterpUniv. hauto lq:on ctrs:InterpExt. *)
(* Qed. *)

(* ----  Backward closure for the interpreted sets ----- *)
Lemma InterpExt_back_clos Ξ i I A PA (hI : forall i A B, I i A -> B ⇒ A -> I i B):
    ⟦ Ξ ⊨ A ⟧ i ; I ↘ PA ->
    forall ℓ0 a b, IOk Ξ ℓ0 a -> (a ⇒ b) ->
              PA ℓ0 b -> PA ℓ0 a.
Proof.
  move => h.
  elim : A PA / h.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:rtc.
  - have ? : forall ℓ0 b0 b1 a, b0 ⇒ b1 -> tApp b0 ℓ0 a ⇒ tApp b1 ℓ0 a
        by hauto lq:on ctrs:Par use:Par_refl.
    hauto l:on ctrs:IOk use:InterpExt_Ok unfold:ProdSpace.
  - move => j h ℓ0 a b ha hr.
    suff : I j b -> I j a by tauto.
    firstorder.
  - hauto lq:on ctrs:InterpExt, rtc.
  - hauto lq:on ctrs:rtc.
  - hauto lq:on ctrs:InterpExt, rtc unfold:SumSpace.
  - sfirstorder.
Qed.


Lemma InterpUnivN_back_clos Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ0 a b, IOk Ξ ℓ0 a -> (a ⇒ b) ->
           PA ℓ0 b -> PA ℓ0 a.
Proof.
  simp InterpUniv.
  apply InterpExt_back_clos.
  hauto lq:on ctrs:rtc use:InterpUnivN_back_preservation_star.
Qed.

Lemma InterpUnivN_back_clos_star Ξ i A PA :
    ⟦ Ξ ⊨ A ⟧ i ↘ PA ->
    forall ℓ0 a b, IOk Ξ ℓ0 a ->
              a ⇒* b ->
           PA ℓ0 b -> PA ℓ0 a.
Proof.
  move => h ℓ0 a b /[swap].
  induction 1. sfirstorder use:InterpUnivN_back_clos.
  hauto lq:on use:iok_preservation, InterpUnivN_back_clos.
Qed.



(* (* ------------------------ adequacy ------------------------------- *) *)

Lemma InterpUnivN_Nat Ξ : ⟦ Ξ ⊨ tNat ⟧ 0 ↘ (fun ℓ a => IOk Ξ ℓ a /\ exists v, a ⇒* v /\ is_nat_val v).
Proof. simp InterpUniv. apply InterpExt_Nat. Qed.

End lr_sig.
