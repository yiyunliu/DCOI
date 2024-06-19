Require Import syntax par imports normalform.

Module Type factorization_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import normalform: normalform_sig lattice syntax par).

Reserved Infix "⤳" (at level 60, no associativity).

Definition notAbs a :=
  match a with
  | tAbs _ _ => false
  | _ => true
  end.

Definition notRefl a :=
  match a with
  | tRefl => false
  | _ => true
  end.

Definition notPack a :=
  match a with
  | tPack _ _ _ => false
  | _ => true
  end.

Inductive LoRed : tm -> tm -> Prop :=
| Lo_Pi0 ℓ0 A0 A1 B :
  A0 ⤳ A1 ->
  (* --------------------- *)
  tPi ℓ0 A0 B ⤳ tPi ℓ0 A1 B
| Lo_Pi1 ℓ0 A B0 B1 :
  nf A ->
  B0 ⤳ B1 ->
  (* --------------------- *)
  tPi ℓ0 A B0 ⤳ tPi ℓ0 A B1
| Lo_Abs ℓ0 a0 a1 :
  a0 ⤳ a1 ->
  (* -------------------- *)
  tAbs ℓ0 a0 ⤳ tAbs ℓ0 a1
| Lo_App0 a0 a1 ℓ0 b :
  notAbs a0 ->
  a0 ⤳ a1 ->
  (* ------------------------- *)
  tApp a0 ℓ0 b ⤳ tApp a1 ℓ0 b
| Lo_App1 a ℓ0 b0 b1 :
  notAbs a ->
  nf a ->
  b0 ⤳ b1 ->
  (* ------------------------- *)
  tApp a ℓ0 b0 ⤳ tApp a ℓ0 b1
| Lo_AppAbs ℓ0 a b :
  (* ---------------------------- *)
  (tApp (tAbs ℓ0 a) ℓ0 b) ⤳ (a [b..])

| Lo_Absurd a b :
  a ⤳ b ->
  (* ---------- *)
  tAbsurd a ⤳ tAbsurd b

| Lo_Eq0 ℓ0 a0 a1 b A :
  a0 ⤳ a1 ->
  (* ---------- *)
  tEq ℓ0 a0 b A ⤳ tEq ℓ0 a1 b A

| Lo_Eq1 ℓ0 a b0 b1 A :
  nf a ->
  b0 ⤳ b1 ->
  (* ---------- *)
  tEq ℓ0 a b0 A ⤳ tEq ℓ0 a b1 A

| Lo_Eq2 ℓ0 a b A0 A1 :
  nf a ->
  nf b ->
  A0 ⤳ A1 ->
  (* ---------- *)
  tEq ℓ0 a b A0 ⤳ tEq ℓ0 a b A1

| Lo_J0 ℓp t p0 p1 :
  p0 ⤳ p1 ->
  (* ---------- *)
  tJ ℓp t p0 ⤳ tJ ℓp t p1

| Lo_J1 ℓp t0 t1 p :
  nf p ->
  notRefl p ->
  t0 ⤳ t1 ->
  (* ---------- *)
  (tJ ℓp t0 p) ⤳ (tJ ℓp t1 p)

| Lo_JRefl ℓp t :
  (* ---------- *)
  tJ ℓp t tRefl ⤳ t

| Lo_Sig0 ℓ0 A0 A1 B :
  A0 ⤳ A1 ->
  (* --------------------- *)
  tSig ℓ0 A0 B ⤳ tSig ℓ0 A1 B

| Lo_Sig1 ℓ0 A B0 B1 :
  nf A ->
  B0 ⤳ B1 ->
  (* --------------------- *)
  tSig ℓ0 A B0 ⤳ tSig ℓ0 A B1

| Lo_Pack0 ℓ a0 a1 b :
  a0 ⤳ a1 ->
  (* ------------------------- *)
  tPack ℓ a0 b ⤳ tPack ℓ a1 b

| Lo_Pack1 ℓ a b0 b1 :
  nf a ->
  b0 ⤳ b1 ->
  (* ------------------------- *)
  tPack ℓ a b0 ⤳ tPack ℓ a b1

| Lo_Let0 ℓ0 ℓ1 a0 a1 b :
  notPack a0 ->
  a0 ⤳ a1 ->
  (* --------------------- *)
  tLet ℓ0 ℓ1 a0 b ⤳ tLet ℓ0 ℓ1 a1 b

| Lo_Let1 ℓ0 ℓ1 a b0 b1 :
  nf a ->
  notPack a ->
  b0 ⤳ b1 ->
  (* --------------------- *)
  tLet ℓ0 ℓ1 a b0 ⤳ tLet ℓ0 ℓ1 a b1

| Lo_LetPack ℓ0 ℓ1 a b c :
  tLet ℓ0 ℓ1 (tPack ℓ0 a b) c ⤳ c[b .: a ..]

| Lo_Down ℓ0 p0 p1 :
  p0 ⤳ p1 ->
  tDown ℓ0 p0 ⤳ tDown ℓ0 p1

| Lo_DownRefl ℓ0 :
  tDown ℓ0 tRefl ⤳ tRefl
where "A ⤳ B" := (LoRed A B).
#[export]Hint Constructors LoRed : lored.
End factorization_sig.

Module Type factorization_facts
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import normalform: normalform_sig lattice syntax par)
  (Import factorization : factorization_sig lattice syntax par normalform).

Lemma LoRed_not_nf a b :
  a ⤳ b -> ~~ (nf a).
  move => h.
  elim : a b / h; hauto inv:tm qb:on.
Qed.

Lemma nf_ne_not_LoRed a b :
  nf a || ne a ->
  ~ a ⤳ b.
Proof.
  elim : a b; sauto b:on.
Qed.

Lemma LoRed_deterministic a b0 b1 :
  a ⤳ b0 ->
  a ⤳ b1 ->
  b0 = b1.
Proof.
  move => h.
  move : b1.
  elim : a b0 / h;
    lazymatch goal with
    | [|- context[tEq]] => idtac
    | _ => hauto lq:on rew:off inv:LoRed use:nf_ne_not_LoRed, LoRed_not_nf b:on
    end.
  - move => > ? ?.
    inversion 1; subst;
      sfirstorder use:nf_ne_not_LoRed, LoRed_not_nf b:on.
  - move => > ? ? ?.
    inversion 1; subst;
      sfirstorder use:nf_ne_not_LoRed, LoRed_not_nf b:on.
  - move => > ? ? ? ?.
    inversion 1; subst;
      sfirstorder use:nf_ne_not_LoRed, LoRed_not_nf b:on.
Qed.

End factorization_facts.
