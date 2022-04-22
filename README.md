# Formal verification of security properties of Morello

This repository contains a mechanised proof that the instruction-set
architecture specification of Morello, a capability-enhanced prototype Arm
architecture, satisfies its main intended security property: reachable
capability monotonicity.  The property and the proof are described in the paper
(available as PDF [here][morello-formal-paper]):

Verified Security for the Morello Capability-enhanced Prototype Arm Architecture.
Thomas Bauereiss, Brian Campbell, Thomas Sewell, Alasdair Armstrong, Lawrence
Esswood, Ian Stark, Graeme Barnes, Robert N. M. Watson, and Peter Sewell.
In ESOP 2022.

The proof was developed using weekly snapshots of the Morello specification
provided by Arm while the architecture was being developed.  It has since been
ported to the [publicly released Morello Sail model][sail-morello], where some
Arm-internal parts of the model that are not architectural, but required to
generate an emulator (in particular the top-level fetch-decode-execute
function), have been replaced by corresponding parts of the [public Sail model
of the Armv8-A architecture][sail-arm] adapted to Morello (e.g. adding
capability checks to instruction fetching).

## Structure

The following files contain hand-written parts of the proof:

* [`CHERI_Instantiation.thy`](CHERI_Instantiation.thy): instantiation of the abstract model
* [`CHERI_Lemmas.thy`](CHERI_Lemmas.thy): helper lemmas about auxiliary functions performing capability manipulations and checks
* [`State_Invariant.thy`](State_Invariant.thy): auxiliary definitions for proving the preservation of invariants
* [`New_CVC4.thy`](New_CVC4.thy): workaround for a version issue with the SMT solver used in the proof of some lemmas
* [`CHERI_Monotonicity.thy`](CHERI_Monotonicity.thy): statement and proof of the monotonicity theorem

Then there are files containing automatically generated lemmas about the bulk
of the architecture (auxiliary functions and instructions).  They are generated
by the `gen_lemmas` tool developed as part of [the CHERI abstraction on which
this proof builds][t-cheri], using information in the file
[`morello.json`](morello.json) about details of the architecture as well as
patches needed for the proofs of specific lemmas.  The following files are
generated (these are distributed with the release tarballs on Github, or can be
freshly generated using the `gen_lemmas` Makefile target):

* `CHERI_Gen_Lemmas.thy`: miscellaneous lemmas about register footprints, functions that do not involve capabilities at all, etc.
* `CHERI_Cap_Properties.thy`: lemmas showing that helper functions and instructions only produce monotonically derivable capabilities (with well-defined exceptions)
* `CHERI_Mem_Properties.thy`: lemmas showing that helper functions and instructions perform the right capability checks when accessing memory
* `CHERI_Fetch_Properties.thy`: lemmas showing that instruction fetching performs the right capability checks (checking for the "Execute" rather than the "Load" permission)
* `CHERI_Invariant.thy`: lemmas showing that helper functions and instructions preserve the invariants used by the monotonicity proof

Note that these are theory files that are checked by Isabelle, so there is no
need to trust the lemma generation tool.

Finally, the file [`properties.sail`](properties.sail) contains key properties
of individual capability manipulating functions, e.g. the monotonicity of
`CapSetBounds`, that were checked using Sail's SMT tooling (uncovering some
bugs in the specification) before the Isabelle proof was developed.

## Dependencies

* [Isabelle 2020](https://isabelle.in.tum.de/website-Isabelle2020/index.html)
* A version of the [Archive of Formal Proofs (AFP)](https://www.isa-afp.org/)
  compatible with Isabelle 2020 ([available here](https://foss.heptapod.net/isa-afp/afp-2020)),
  specifically the `Word_Lib` library
* [Sail][sail] (last checked with revision `5d18bd95`)
* The [Sail Morello model][sail-morello]
* The [CHERI abstraction used for the proof][t-cheri]

## Running the proof

With the auto-generated lemma files in place (either downloaded as part of a
Github release, or generated using the `gen_lemmas` Makefile target), the
`check_proof` Makefile target runs the Isabelle proof (you might have to
override some variables pointing to the location of dependencies, e.g.
`AFP_DIR`).

Note that the proof might run for several hours (on an i7-10510U CPU at
1.80GHz, it ran in around 7.5h CPU time / 3.5h real time, with peak memory
consumption of 18GB).

## Licence

This proof is distributed under the BSD 2-clause licence in [`LICENCE`](LICENCE).

[sail]: https://github.com/rems-project/sail
[sail-morello]: https://github.com/CTSRD-CHERI/sail-morello
[sail-arm]: https://github.com/rems-project/sail-arm
[t-cheri]: https://github.com/CTSRD-CHERI/t-cheri
[morello-formal-paper]: https://www.cl.cam.ac.uk/~pes20/morello-proofs-esop2022.pdf
