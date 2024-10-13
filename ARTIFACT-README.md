# POPL 2025 Artifact

Name:    **Consistency of a Dependent Calculus of Indistinguishability**

## Artifact Instructions
You can open up the [html version](README.html) of the document in a
web browser to make use of the hyperlinks.

### Quickstart guide
If you want to replicate
the environment on your host machine, you
can refer to the section [Steps to recreate the artifact
environment](#steps-to-recreate-the-artifact-environment) to install
the necessary dependencies. The rest of the instructions assume that
the commands are executed from within the VM. You should adjust the
paths accordingly to match the location of the artifact directory on
your host machine.

If you want to validate the proofs and run the prototype
type checker through the provided image, you can follow the
[Installation instructions](#installation) to set up QEMU. The guest
system is Arch Linux. You can use the `pacman` command to install
additional packages if needed.

If you have followed the instructions successfully, you should now
have access to a terminal with the following prompt.
```sh
[dcoi@popl25 ~]$
```

Note: The guest system is in x86-64. If your host system has an ARM
processor, then it's normal for the VM to run a lot slower since QEMU
would need to emulate x86 instructions.

#### Proof scripts
To use Coq to verify the claims from the paper, run the following command in the terminal:
```sh
cd ~/artifact/proofs
make clean
make
```
Optionally, you can pass the `-j[jobs]` flag to `make` where `[jobs]`
is replaced by an integer representing the number of the jobs
that you want to run in parallel. This can reduce the build time
significantly. However, since the VM by default has only 4 GiB of memory,
running too many jobs simultaneously can cause the `coqc` compiler to
be killed. If that happens, you should decrease the number you pass to `-j`.

Note: On a Linux machine with Intel 12700k, the development took 2
minutes 15 seconds to compile with `make`.

A successful compilation should produce the following output, which
should include signatures of the top-level claims and the
axioms they depend on near the end.
```sh
as2-exe -i syntax.sig -p UCoq > theories/Autosubst2/syntax.v
perl gen_syntax.pl
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
make[1]: Entering directory '/home/dcoi/artifact/proofs'
COQDEP VFILES
COQC theories/Autosubst2/axioms.v
COQC theories/Lattice/All.v
COQC theories/Autosubst2/unscoped.v
# ... omitted ...
dcoi_with_nat_lattice.conv_dec.conv_dec
     : forall (Γ : dcoi_with_nat_lattice.typing.context)
         (A B : dcoi_with_nat_lattice.syntax.tm)
         (h0 : dcoi_with_nat_lattice.typing.Wt Γ ?ℓ ?a A)
         (h1 : dcoi_with_nat_lattice.typing.Wt Γ ?ℓ0 B
                 (dcoi_with_nat_lattice.syntax.tUniv ?i)),
       reflect
         (dcoi_with_nat_lattice.conv.conv
            (dcoi_with_nat_lattice.typing.c2e Γ) A B)
         (dcoi_with_nat_lattice.conv_dec.convb Γ A B h0 h1)
where
?ℓ : [ |- nat_lattice.T]
?ℓ0 : [ |- nat_lattice.T]
?i : [ |- fin]
?a : [ |- dcoi_with_nat_lattice.syntax.tm]
Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
```
It's normal to see some warnings in the output. The execution is
successful as long as the last part of the output matches the one
shown above.

#### Prototype implementation
Run the following command to switch to the directory containing the prototype implementation:
```sh
cd ~/artifact/impl
```
The directory contains the source code of the prototype
implementation, written in Haskell.
A binary executable of the type checker has already been compiled and
installed into the image. You can run the type checker by invoking the
command `dcoi`.

Note: To reduce the size of the image, we stripped the Haskell
toolchain from the image and only kept the statically linked `dcoi`
executable. If you want to compile the executable from scratch, you
should install the Haskell toolchain through `ghcup` or the `pacman`
package manager and run `stack build` in `impl`.

The directory [pi](impl/pi) contains the examples. To type check a
file, simply run the `dcoi` command with the file name passed in as an
argument.
```sh
dcoi pi/Equal.pi
```
The above command should produce the following output.
```sh
[dcoi@popl25 pi]$ dcoi Equal.pi
================================================================================
processing Equal.pi...
Parsing File "Equal.pi"
type checking...
Checking module "Equal"
module Equal where

data Eq (A : Type) (a : A) (b : A) : Type where
  EqRefl of [a = b]
j : (A : Type) -> (a1 : A) -> (a2 : A) -> (a : Eq A a1 a2) -> (B : (x : A) -> Eq A x a2 -> Type) -> (b : B a2 EqRefl) -> B a1 a
j = \ A a1 a2 a B b. case a of
                       EqRefl => b
sym : (A : Type) -> (x : A) -> (y : A) -> Eq A x y -> Eq A y x
sym = \ A x y pf. case pf of
                    EqRefl => EqRefl
trans : (A : Type) -> (x : A) -> (y : A) -> (z : A) -> Eq A x z -> Eq A z y -> Eq A x y
trans = \ A x y z pf1 pf2. case pf2 of
                             EqRefl => pf1
```
Running `make` under the directory [pi](impl/pi) will invoke `dcoi` on
all the `.pi` files.


### Step-by-step instructions
#### Complete claims made by the paper substantiated by this artifact
This artifact has two components: a Coq development and a Haskell prototype
implementation of DCOI.

The Coq development substantiates the results claimed in the paper as indicated by
the footnotes. All results are proved about DCOI$^\omega$, presented in
Sections 3-5.

The code examples presented in Section 2 can be found in
[impl/pi/Paper.pi](impl/pi/Paper.pi) and can be checked by the
prototype typechecker `dcoi`.

#### Coq Development
##### System specification
The file
[proofs/theories/Lattice/All.v](proofs/theories/Lattice/All.v) defines
the specification of a lattice structure as a module type.
We parameterize our development over this lattice structure by placing
most of our the definitions and proofs inside Coq module functors.

We use the `autosubst2` tool to convert the HOAS syntax specification
of DCOI ([syntax.sig](proofs/syntax.sig)) into a Coq file containing
its de Bruijn representation
([syntax.v](proofs/theories/Autosubst2/syntax.v)). The generated Coq
file includes not only the inductive definition of the term syntax
`tm`, but also the renaming (`ren_tm`) and substitution (`subst_tm`)
functions. The notation `a[σ]` (resp. `a⟨ξ⟩`) represents the application of
a substitution `σ` (resp. a renaming `ξ`) to the term `a`.
Since `autosubst2` doesn't support module functors, we use [a perl script](proofs/gen_syntax.pl) to wrap the generated syntax inside a functor.

The typing rules can be found in
[typing.v](proofs/theories/typing.v). The inductive types `Wt` and
`Wff` represent well-typedness and context well-formedness
respectively. Every rule with an admissible premise in the text is
accompanied by a lemma that justifies the admissible version of
rule. We include those lemmas in our claimed results section.

The definition of untyped convertibility used in rule `WT-Conv` (the
`T_Conv` constructor in the Coq file) can be found in
[conv.v](proofs/theories/conv.v). The indistinguishability judgment
is named `IEq` and can be found in [geq.v](proofs/theories/geq.v).

##### Instantiated lemmas
To ensure that we did not accidentally parameterize our development
over an inconsistent assumption, we instantiate the
module functors to a concrete lattice in the file
[toplevel.v](proofs/theories/toplevel.v).

In [toplevel.v](proofs/theories/toplevel.v), we print out the
signatures of the top-level theorems and the axioms they depend on. By
instantiating the module functors, we ensure that the parameterized
lattice structure does not appear alongside the axioms we actually used.

Reviewers can refer to 
[Axioms made in the Coq
development](#axioms-made-in-the-coq-development) for a detailed
discussion of the use of axioms.

##### Key results
The individual results can be found in the corresponding Coq files and theorem
statements as directed by the paper's footnotes. All Coq files are in
the directory `/home/dcoi/proofs` inside the image and we also duplicate the
same files in the `proofs` subdirectory of the tarball so they can be
more easily accessed through the host machine and navigated through
this README file.

- Lemma 3.1 (Regularity)
  - [preservation.v](proofs/theories/preservation.v):`Wt_Wff`, `Wt_regularity`

- Lemma 3.2 (Simulation)
  - [conv.v](proofs/theories/conv.v):`simulation_star`
  
- Admissibility of the premises in `Wt-Abs`, `Wt-J`, `Wt-Let`
  - [preservation.v](proofs/theories/preservation.v): `T_Abs_simpl`,
    `T_J_simpl`, `T_Let_simpl`
	
- Admissibility of `Wt-Proj1`, `Wt-Proj2`, `Wt-Proj2Alt`, `Wt-T`, `Wt-Box`, `Wt-Unbox`
  - [admissible.v](proofs/theories/admissible.v):`T_Proj1`, `T_Proj2`, `T_Proj2_Alt`,
    `T_T`, `T_Box`, `T_Unbox`

- Lemma 3.3 (Downgrade)
  - [admissible.v](proofs/theories/admissible.v): `T_Down_Alt`
  
- Figure 11 `L-Subst`, `L-Sub`, `I-Subst`, `I-Cong`, `I-Down`:
  - [geq.v](proofs/theories/geq.v): `iok_subst`, `iok_subsumption`,
    `ieq_iok_subst`, `ieq_morphing_mutual`, `ieq_downgrade_mutual`

- Figure 11 `Wt-Subst`, `Wt-Sub`:
  - [preservation.v](proofs/theories/preservation.v): `subst_Syn`, `subsumption`

- Lemma 4.1 (Diamond)
  - [par.v](proofs/theories/par.v): `Par_confluent`
  
- Lemma 4.2 (Confluence)
  - [par.v](proofs/theories/par.v): `Pars_confluent`

- Lemma 4.3 (Transitivity of Equality)
  - [conv.v](proofs/theories/conv.v): `conv_trans`

- Lemma 4.4
  - [preservation.v](proofs/theories/preservation.v): `Wt_Refl_Coherent`

- Lemma 4.5 (Type Preservation)
  - [preservation.v](proofs/theories/preservation.v):
    `subject_reduction(_star)`
	
- Definition 5.1 (Weakly normalizing terms)
  - [normalform.v](proofs/theories/normalform.v): `wn`, `wne`

- Lemma 5.2
  - [normalform.v](proofs/theories/normalform.v): `nf_refl`
  
- Figure 12 (Definition of the logical predicate)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpExt`

- Lemma 5.4 (Escape)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUniv_Ok`

- Lemma 5.5 (Subsumption for the logical predicate)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUnivN_subsumption`

- Lemma 5.6 (Inversion of the logical predicate)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUnivN_Eq_inv`,
    `InterpUnivN_Fun_inv_nopf`, `InterpUnivN_Void_inv`

- Lemma 5.7 (Backward closure)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUnivN_back_clos`

- Lemma 5.8 (Cumulativity)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUnivN_cumulative`

- Lemma 5.9 (Reduction preserves interpretation)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUnivN_preservation`

- Lemma 5.10 (Functionality)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUnivN_deterministic`

- Lemma 5.11 (Functionality for indistinguishable terms)
  - [semtyping.v](proofs/theories/semtyping.v): `InterpUnivN_Eq`

- Lemma 5.12 (Antirenaming for parallel reduction)
  - [normalform.v](proofs/theories/normalform.v): `Par_antirenaming`

- Lemma 5.13 (Antirenaming for normal and neutral forms)
  - [normalform.v](proofs/theories/normalform.v): `ne_nf_renaming_with_d`

- Lemma 5.14 (Antirenaming for weak normalization)
  - [normalform.v](proofs/theories/normalform.v): `wn_antirenaming`

- Lemma 5.15 (Adequacy)
  - [semtyping.v](proofs/theories/semtyping.v): `adequacy`

- Definition 5.17 (Valid substitutions)
  - [soundness.v](proofs/theories/soundness.v): `ρ_ok`
  
- Lemma 5.18
  - [soundness.v](proofs/theories/soundness.v): `iok_ρ_ok_morphing`

- Lemma 5.19 (Structural rules for valid substitutions)
  - [soundness.v](proofs/theories/soundness.v): `ρ_ok_id`, `ρ_ok_cons`

- Definition 5.20 (Semantic well-typedness)
  - [soundness.v](proofs/theories/soundness.v): `SemWt`

- Lemma 5.21 (Weakening for valid substitutions and semantic
  well-typedness)
  - [soundness.v](proofs/theories/soundness.v): `ρ_ok_renaming`, `weakening_Sem`

- Theorem 5.22 (Fundamental theorem)
  - [soundness.v](proofs/theories/soundness.v): `soundness`
  
- Corollary 5.23 (Weak normalization for well-typed terms)
  - [soundness.v](proofs/theories/soundness.v): `normalization`

- Corollary 5.24 (Logical consistency)
  - [consistency.v](proofs/theories/consistency.v): `consistency`

- Lemma 5.25 (Standardization)
  - [factorization.v](proofs/theories/factorization.v): `standardization`

- Corollary 5.26 (Normalization is decidable)
  - [factorization.v](proofs/theories/factorization.v): `LoRed_normalize`

- Lemma 5.27 (Indistinguishability is decidable)
  - [geq.v](proofs/theories/geq.v): `IEq_dec`

- Definition 5.28 (Algorithm for type conversion)
  - [iconv_dec.v](proofs/theories/iconv\_dec.v): `convb`

- Theorem 5.29 (Decidability of type conversion with bottom)
  - [iconv_dec.v](proofs/theories/iconv\_dec.v): `conv_dec`

- Theorem 5.30 (Decidability of indexed type conversion)
  - [iconv_dec.v](proofs/theories/iconv\_dec.v): `iconv_dec`

##### Differences between the mechanization and the paper presentation
In Coq, inductively generated types and propositions must be defined
at the top-level. The definition of the logical predicate, on the
other hand, is a recursive function (over the universe levels) that
returns an inductive proposition. In an ideal world, we would want to
define our logical relation as follows.
```coq
Fixpoint InterpUnivN Ξ (n : nat) ... :=
  Inductive InterpUniv Ξ := ...
  | ...
```
Instead, we need to factor this definition into two parts. First, we
define the top-level inductive type `InterpExt Ξ n I`. The
parameter `I` is a function representing the recursive call, which
gives the interpretation of types at universe levels that are strictly
lower than `n`. We then tie the knot by defining a recursive function
`InterpUnivN Ξ n` over `n`, which simply calls `InterpExt` with `I`
instantiated to itself. The function `InterpUnivN` gives us the
logical predicate we wanted.

##### Axioms made in the Coq development
To check the axioms used in the development, the reviewers can run the
`Print Assumptions` command in [toplevel.v](proofs/theories/toplevel.v) to
query the axioms used in the instantiated modules.
```coq
Print Assumptions dcoi_with_nat_lattice.consistency.consistency.
```
Here's the output.
```sh
Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
```

The command `make validate` runs `coqchk` to dump all axioms used in our development.
```
make -f CoqMakefile validate
make[1]: Entering directory '/home/dcoi/proofs'
"coqchk" -silent -o  -R theories DCOIOmega theories/Autosubst2/axioms.vo theories/Autosubst2/syntax.vo theories/Autosubst2/unscoped.vo theories/Lattice/All.vo theories/admissible.vo theories/consistency.vo theories/conv.vo theories/factorization.vo theories/geq.vo theories/iconv_dec.vo theories/imports.vo theories/normalform.vo theories/par.vo theories/preservation.vo theories/semtyping.vo theories/soundness.vo theories/toplevel.vo theories/typing.vo theories/typing_conv.vo

CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Axioms:
    Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
    Coq.Reals.ClassicalDedekindReals.sig_not_dec
    Coq.Reals.ClassicalDedekindReals.sig_forall_dec
    Coq.Logic.PropExtensionality.propositional_extensionality
    Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
  
make[1]: Leaving directory '/home/dcoi/proofs'
```
Note that we don't actually use `eq_rect_eq` or the axioms about
dedekind reals in our development. They are never printed when we run
the `Print Assumptions` command. `coqchk` is known to report axioms
that are part of external modules despite them not being used by the
development.

Functional and propositional extensionality allow us to recover the
type of reasoning in set theory where two sets are considered equal if
and only if they contain the same elements (in Coq, the predicate `A
-> Prop` can be thought of as a subset of the type `A`). These two
axioms are known to be consistent with Coq.

The introduction of axioms in the `Prop` sort means that we can no
longer prove decidability of a proposition `P` by providing an
inhabitance of `P \/ not P` since types in `Prop` lose canonicity. Instead, in
our development, we explicitly define a computable function in the
relevant universe `Type` and use the ssreflect's `reflect` type to
connect between the function and the proposition it's meant to decide.

##### Extending the system
To extend DCOI$^\omega$ with extra features, one can modify
[syntax.sig](proofs/syntax.sig) to add new syntactic forms to the grammar and add
new rules for the typing and equality judgments in
[typing.v](proofs/theories/typing.v) and [geq.v](proofs/theories/geq.v).


#### Prototype implementation
The file [impl/README.pi](impl/README.pi) contains the details
related to the prototype implementation. The differences between the
syntax from the text and the actual syntax used by the prototype is
also detailed in the linked documentation.

The examples in Section 2 can be found in
[impl/pi/Paper.pi](impl/pi/Paper.pi).

## QEMU Instructions

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.


#### Windows 10/11

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.


### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM.

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `dcoi`. The default
username is `dcoi`.

```
$ ssh -p 5557 dcoi@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5557 dcoi@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```

### Reset the state of the VM

If you corrupted the VM state by accident, you can simply reset the VM
state through QEMU's snapshot feature.
```sh
qemu-img snapshot -a initial-state disk.qcow2
```

## Steps to recreate the artifact environment
This section describes how to recreate the artifact environment 
on your host machine.

First, install the following packages on your system. We provide the
version numbers on our machine for reference, though other versions
might also work.

For the Coq development:

- opam 2.1.5

For the prototype typechecker:

- cabal-install 3.6.2
- GHC 9.2.8
- z3 4.13.0

Note: If your distribution is Arch Linux, we recommend that you
install the GHC and cabal using `ghcup`. If installed through the
package manager, you need to follow the instructions on the [wiki
page](https://wiki.archlinux.org/title/Haskell) to configure `cabal`
or else compilation will fail.

### Install the Coq switch
If it's your first time installing `opam`, you need to run the
following command to initialize it.
```sh
opam init -a --bare
```
Once `opam` is initialized, the next step is to import the switch
configuration used to build the Coq development.

First, switch to the artifact directory containing the Coq development:
```sh
cd artifact/proofs
```
You can run the following command to
create a switch named `dcoi` with the all the required dependencies installed:
```sh
opam switch create dcoi 4.14.2
eval $(opam env --switch=dcoi)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y --deps-only .
```
Note: It might take a few minutes for the installation to finish.

If the installation was successful, the following command should print
the help message of the Coq executable.
```sh
coqc --help
```

### Install autosubst
This section can be skipped if you don't plan to extend the Coq
development by modifying the syntax file
[syntax.sig](proofs/syntax.sig).

Run the following command to clone the autosubst 2 repository.
```sh
git clone https://github.com/uds-psl/autosubst2
```
Run the following command to build the autosubst 2 and copy the
executable to a location `DIR` that's available in your `PATH`.
```sh
cd autosubst2
# Remove the malformed part of the cabal file
sed -i 52,63d as2.cabal 
# Install with cabal
cabal install --installdir=DIR --install-method=copy
```
Remember to replace `DIR` with the location you want the executable to
be copied into.

If `as2-exe` was built successfully and available in your `PATH`,
then the following command should print out the help messages of Autosubst2.
```sh
as2-exe -h
```

The Makefile of the Coq development will invoke `as2-exe` to
regenerate the syntax file if the syntax specification
([syntax.sig](proofs/syntax.sig)) is changed.

### Build and install the prototype type checker
The following command builds the dcoi implementation and places the
executable under the directory `DIR`.
```sh
cd artifact/impl
cabal install --installdir=DIR --install-method=copy
```
Again, make sure to replace `DIR` in the command above with a
directory that is part of your `PATH` environment variable so you can
invoke the prototype typechecker `dcoi` directly in your command line.

This completes the local setup instruction. You can now follow the
instructions from [Quickstart guide](#quickstart-guide) to validate the
Coq development and type check programs with the prototype implementation.
