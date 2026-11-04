# Lean proofs of the semigroup laws of order at most five

The result of [`results/semigroup5_truncated_seeded`](../results/semigroup5_truncated_seeded) in the ETP's form, against the ETP's library at the commit `lakefile.toml` pins. The laws are its `EquationN`; those it does not declare are declared with its `equation` command and numbered by its scheme. Each certificate is a theorem `EquationA_B_implies_EquationC`, an `@[equational_result]` if it has one hypothesis. Each semigroup is a `finOpTable` with an `@[equational_result]` theorem `∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [satisfied] [refuted]`. `lean_etp.py` writes the Lean files, `Order5/` and `Order5.lean`, from the results and their certificates; `verify.py --lean` checks that their statements give the result. Several results can share a project, each in its own module (see [the exploration's README](../README.md)).

Build outside folders that a cloud service syncs, with [Lean](https://lean-lang.org) 4.29.1, which `elan` installs from `lean-toolchain`: copy the project files to a directory `LEAN_DIR`, fetch the ETP and Mathlib's build, write the Lean files, build them and check their statements:

```bash
cp explorations/equational_theories/lean_order5/{lakefile.toml,lean-toolchain,lake-manifest.json,.gitignore} LEAN_DIR
(cd LEAN_DIR && lake exe cache get)
R=explorations/equational_theories/results/semigroup5_truncated_seeded
python explorations/equational_theories/lean_etp.py $R $R/certificates.jsonl.xz --etp LEAN_DIR/.lake/packages/equational_theories -o LEAN_DIR --classes
(cd LEAN_DIR && lake build)
python explorations/equational_theories/verify.py $R --lean LEAN_DIR/Order5 --etp LEAN_DIR/.lake/packages/equational_theories --classes
```

The build takes about 12 hours of CPU time, most of it in `Order5/SemigroupParts*`, which decide in parts the laws too costly to decide at once. Lake runs one Lean process per core, each needing up to about 5 GB; with less memory, build the modules a few at a time, such as `lake build Order5.SemigroupParts0 Order5.SemigroupParts1`.
