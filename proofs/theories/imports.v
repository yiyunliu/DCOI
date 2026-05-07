From Stdlib Require Export ssreflect ssrbool List.
From Stdlib Require Export Logic.PropExtensionality
  (propositional_extensionality) FunInd.
From Stdlib Require Import Logic.FunctionalExtensionality Program.Tactics.
From Equations Require Export Equations.
From Hammer Require Export Tactics.
From stdpp Require Export relations (rtc, rtc_transitive, rtc_once, rtc_inv, rtc(..), diamond, confluent, diamond_confluent, sn) base(sum_relation(..)).
From Stdlib Require Export Psatz.

Global Set Warnings "-notation-overridden".
Require Export Autosubst2.syntax.

(* The new autosubst-ocaml [asimpl] guards itself with [check_no_evars] —
   this rejects goals that still have unresolved evars from a partial
   [eapply]. Many existing proofs relied on the old [asimpl] running anyway
   and resolving the evars through unification with rewrite results. Shadow
   the guard with a no-op so legacy proofs continue to work. *)
Ltac check_no_evars := idtac.

(* Functional extensionality tactic — provided by the old as2-exe-generated
   axioms.v header but no longer present in autosubst-ocaml. Re-introduce it
   so existing proofs continue to work. *)
Tactic Notation "nointr" tactic(t) :=
  let m := fresh "marker" in
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (refine (@functional_extensionality_dep _ _ _ _ _) ||
     refine (@forall_extensionality _ _ _ _) ||
     refine (@forall_extensionalityP _ _ _ _) ||
     refine (@forall_extensionalityS _ _ _ _)); intro
  end).
