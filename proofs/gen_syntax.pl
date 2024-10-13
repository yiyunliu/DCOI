#!/usr/bin/perl
use strict;
use warnings;
use utf8;
binmode(STDOUT, ":utf8");

my $prelude = <<'END_PRELUDE';
Require Export Lattice.All.
Require Export unscoped.

Module Type syntax_sig
  (Export lattice : Lattice).
END_PRELUDE

my $prologue = <<'END_PROLOGUE';

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity) : subst_scope.

Global Disable Notation "'var'" : subst_scope.
Global Disable Notation "↑".
Global Open Scope subst_scope.

End syntax_sig.
END_PROLOGUE

open(my $fh, "<:encoding(UTF-8)", "theories/Autosubst2/syntax.v") or die "Can't open syntax file";

my $syntax = join('',map { (my $s = $_) =~ s/^(Hint|Instance)/#[export]$1/; $s } grep(!/^Require Export/,<$fh>));

close $fh;
$syntax =~ s/\(\(fun \w+ => \(eq_refl\) \w+\) \w+\)/eq_refl/g;

open($fh, ">:encoding(UTF-8)", "theories/Autosubst2/syntax.v") or die "Can't open syntax file";
print $fh $prelude , $syntax, $prologue;
