#!/usr/bin/perl
# Post-process the autosubst-ocaml-generated syntax.v so that it becomes a
# Module Type parameterized by a Lattice, exposing the lattice's `T` to the
# inductive definition of `tm`.
use strict;
use warnings;
use utf8;
binmode(STDOUT, ":utf8");

my $prelude = <<'END_PRELUDE';
Require Export Lattice.All.
Require Export core unscoped.
Require Import Setoid Morphisms Relation_Definitions.

(* Equations (transitively required by Lattice.All) marks both arguments
   of [eq_refl] implicit, which breaks the autosubst-ocaml-generated terms
   of the form [(eq_refl s0)]. Restore the legacy alternative arity. *)
#[global] Arguments eq_refl {A}%_type_scope {x}%_type_scope, [_] _.

Module Type syntax_sig
  (Export lattice : Lattice).
END_PRELUDE

my $prologue = <<'END_PROLOGUE';

(* Backwards compatibility with the old as2-exe-generated header. *)
Notation fin := nat (only parsing).

(* Bring the autosubst-generated [.:], shift, and other helper notations
   into scope. Without this they live inside the [UnscopedNotations] module
   and cannot be seen by the proofs. *)
Include UnscopedNotations.

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

Global Disable Notation "'var'" : subst_scope.
Global Disable Notation "↑".
Global Open Scope subst_scope.

End syntax_sig.
END_PROLOGUE

my $path = "theories/Autosubst2/syntax.v";

open(my $fh, "<:encoding(UTF-8)", $path) or die "Can't open syntax file: $!";
# Drop the autosubst-ocaml header `Require Import core unscoped.` and the
# duplicate `Require Import Setoid Morphisms Relation_Definitions.` — we
# emit Setoid/Morphisms/Relation_Definitions from the prelude.
my $syntax = join('', grep { !/^Require Import (?:core unscoped|Setoid Morphisms Relation_Definitions)\.\s*$/ } <$fh>);
close $fh;

# Inside `Module Type syntax_sig`, Rocq's elaborator cannot recover the
# dependent return type of pattern matches whose type is `subst_tm sigma s = s`
# (or similar) just from the branches — `tm` and its constructors are treated
# more abstractly. Add explicit `return ...` clauses to the matches in
# Fixpoints whose result type is an equation, so the elaborator does not have
# to guess.
$syntax =~ s/^(Fixpoint\s+\w+[^{]*?\{struct\s+s\}\s*:\s*\n)(.+?)(\s*:=\s*\n\s*match s)(\s+with)/$1$2$3 return $2$4/gms;

# Drop the [check_no_evars] guard from autosubst-ocaml's [asimpl] tactic.
# Many existing proofs intentionally leave evars in the goal and rely on
# [asimpl]'s rewriting + unification to fix them up; the new guard rejects
# those goals outright.
$syntax =~ s/^Ltac asimpl := check_no_evars;/Ltac asimpl :=/m;

open($fh, ">:encoding(UTF-8)", $path) or die "Can't open syntax file: $!";
print $fh $prelude, $syntax, $prologue;
close $fh;
