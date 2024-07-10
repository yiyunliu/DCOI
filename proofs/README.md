# Mechanized proofs for DCOI Omega
## Installing dependencies
If you want to change the syntax specification
[syntax.sig](syntax.sig), you need to install [Autosubst
2](https://github.com/uds-psl/autosubst2) to regenerate the
Coq syntax file [syntax.v](theories/Autosubst2/syntax.v).

All Coq related dependencies are specified in the
[dcoi-omega.opam](dcoi-omega.opam). You can install the dependencies
by running the following command:
```sh
opam install --deps-only .
```

Alternatively, if you want to match the exact opam switch state we use
to run the proofs, you can import the switch file to replicate our
environment:
```sh
opam switch import dcoi-omega.switch --switch [SWITCHNAME] \
 --repositories=coq-released=https://coq.inria.fr/opam/released,default=https://opam.ocaml.org
```
The `[SWITCHNAME]` should be replaced by the name you want for the switch.

## Validating the proofs
The following command validates the proofs with 4 threads running in
parallel. On our machine, this command took 90 seconds to finish.
```sh
make -j4
```
Coq can take up a lot of memory, so you might want to reduce the
number passed to `-j` if your memory runs out.

If run successfully, the command will print out the assumptions used
in the top-level theoreoms for subject reduction, normalization,
consistency, and decidability of indexed type conversion. The axioms
should include only `functional_extensionality_dep` (functional
extensionality) and `propositional_extensionality` (propositional
extensionality). The results are otherwise closed under assumptions.

Alternatively, if you want to be *really* sure, you can run `coqchk`
with the following command:
```sh
make -j4 validate
```
This command takes 133 seconds to finish (after we have already
generated the `.vo` files) on our machine, and gives the following
output:
```
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
```
Compared to `Print Assumptions`, the `coqchk` command reports more
axioms as it also includes the ones that are imported but not used.


## Parameterized lattice structure
Most files define functors that are parameterized by a lattice
structure. To make sure we do not accidentally mess up our lattice
definition and introduce a false axiom, we instantiate all these
functors in the file [toplevel.v](theories/toplevel.v) with a natural
number lattice before we print out the assumptions. Checking the
[toplevel.v](theories/toplevel.v) should transitively check all the
proofs in this development.
