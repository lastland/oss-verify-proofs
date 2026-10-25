# How a proof is checked

The verdict on a proof is one command, `oft check`, run in the checker image
that [release.yaml](../release.yaml) names (`images.checker`). This page says
what that command does, which Rocq it uses, how it audits axioms, and what CI
runs.

## Rocq

The checker image holds the official Rocq 9.2.0 (opam packages `rocq-runtime`,
`rocq-core` and `rocq-stdlib` at 9.2.0), LPS at the commit that release.yaml
names (`semantics.commit`) with its `elf-snapshot` tool, and the libraries that
LPS and the proofs use: stdpp 1.13.0, Flocq 4.2.2 and rocq-read-file 0.0.2. It
also holds dune and Python 3. It holds no proof automation
([toolchain/checker.Dockerfile](../toolchain/checker.Dockerfile)). The base
image is pinned by digest, the Rocq opam repository by commit, every opam
package by version and checksum, and the LPS files by a hash over them. The
Ubuntu packages that the image installs (libgmp-dev, pkg-config, m4, python3
and time) are not pinned.

The proofs load their libraries with plain `Require`. The kernel checks every
term as `rocq compile` builds it.

## What `oft check` does

For each harness that it checks, `oft check`:

1. checks every binary against its SHA-256 in `harness.yaml`;
2. builds the memory images from the ELF files, then `Images.v`,
   `Statements.v` and `Characterise.v`;
3. compiles the shared proof library, `proofs/lib/`, when present, then the
   harness's proof library, `proofs/<project>/<harness>/lib/`, if it has one,
   and then each proof. Each library is compiled from source once per check
   run; a shared-library failure fails every dependent proof. The shared
   namespace, `OssFuzzTheorems.Proofs.Shared`, is on the loadpath of harness
   libraries, proofs, wrappers and `rocqchk`. In CI this runs under
   `docker run --network none`, so it has no network;
4. compiles a wrapper that it writes itself. The wrapper gives the proof's
   theorem the type of the statement, and prints what the result assumes:

       (* written by oft check; never supplied by a pull request *)
       Require OssFuzzTheorems.zlib.checksum_fuzzer.Statements.
       Require OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.
       Definition certified : OssFuzzTheorems.zlib.checksum_fuzzer.Statements.plain_halts
         := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.plain_halts_holds.
       Set Printing Fully Qualified.
       Print Assumptions certified.

   A proof of any other statement does not type-check. The proof and its
   libraries are compiled from their `.v` files only, against the statements
   that `oft check` built, so a proof written against an edited statement does
   not type-check either;
5. audits the output of `Print Assumptions` (below).

By default, `oft check` also runs each counterexample under qemu-riscv64. The
checker image has no qemu, so CI runs `--parts statements,proofs` in the
checker image and `--parts counterexamples` in the runner image.

In CI, `oft lint`, `oft plan` and `oft check` always run from the base branch
of a pull request, never from the pull request. The statements also come from
the base branch, except in a release pull request, which changes the facts on
purpose ([pr.yml](../.github/workflows/pr.yml)).

## Axioms

[toolchain/allowed-axioms.txt](../toolchain/allowed-axioms.txt) lists every
axiom that a proof may use:

- the primitive 63-bit integers, arrays and strings of Rocq, and the axioms
  that specify them (`Corelib.Numbers.Cyclic.Int63.*`, `Corelib.Array.*`,
  `Corelib.Strings.*`);
- six axioms of the standard library: `Classical_Prop.classic`,
  `FunctionalExtensionality.functional_extensionality_dep`,
  `IndefiniteDescription.constructive_indefinite_description`,
  `PropExtensionality.propositional_extensionality`, and
  `ClassicalDedekindReals.sig_forall_dec` and `sig_not_dec`.

The audit is the function `wrapper_assumptions` in
[tools/oft/check.py](../tools/oft/check.py), about 30 lines of Python. It reads
the output of `Print Assumptions` for the wrapper:

- "Closed under the global context" means that nothing is assumed.
- Each entry under "Axioms:" must be a name in the allowed list.
- Everything else is refused: an inductive type assumed positive, a fixpoint
  assumed guarded, an unsafe universe hierarchy, definitional UIP, a change to
  the logic, and output that it cannot read.

A proof may not declare an `Axiom` or a `Parameter` or end in `Admitted`.
`oft lint` refuses these on sight. An `Admitted` lemma is an axiom, so the
audit would refuse a proof that uses one in any case.

## `rocqchk`

`rocqchk` is not part of the verdict, and CI does not run it. `oft check
--rocqchk` adds it as an independent second check of the compiled libraries:
`rocqchk -o -bytecode-compiler no`, once per harness over its statements and
once per harness over the wrappers of all its proofs and their closure, with
every axiom that it reports checked against the allowed list. Without its
bytecode machine, `rocqchk` checks every `vm_compute` by reduction, which can
take hours for the proofs of one harness. With the bytecode machine on,
`rocqchk` 9.2.0 refuses every library that holds a
primitive string, and it runs the bytecode stored in each compiled file instead
of compiling it from the checked terms. Both problems are fixed upstream after
9.2.0 ([rocq-prover/rocq#22361](https://github.com/rocq-prover/rocq/pull/22361),
[#22353](https://github.com/rocq-prover/rocq/pull/22353)).

## Stack size

Rocq runs with the largest stack that the system allows, because large proof
terms overflow the usual 8 MiB stack. [tests/check.sh](../tests/check.sh)
does the same with `ulimit -s unlimited`. This changes where the kernel runs,
not what it checks.

## What CI runs

| workflow | when | what |
|---|---|---|
| [release-check](../.github/workflows/release-check.yml) | each push to `main`, once a week, and on request | every committed proof, with `oft check` in the checker image; the badge on the README shows its result |
| [pr](../.github/workflows/pr.yml) | each pull request, and each push to `main` | `oft lint`, `oft generate --check`, the tests of `tools/oft`, the controls in `tests/`, and `oft check` on each harness that the change affects (every harness when it changes `theories/`, `toolchain/` or `dune-project`) |
| [weekly](../.github/workflows/weekly.yml) | once a week, after each release, and on request | every statement and every proof, with no cache (while the repository is private, each scheduled run checks a third of the harnesses in turn); a byte-for-byte comparison of ELF snapshots made on two kinds of machine; a fresh download and hash of every release asset that the facts pin by SHA-256 |

Every counterexample and its control input are run again in the runner image,
and a counterexample that stops reproducing fails CI.

[tests/check.sh](../tests/check.sh) runs the same check on the toy controls in
`tests/`. It fails if a control that must be refused is accepted, or if it is
refused for the wrong reason.
