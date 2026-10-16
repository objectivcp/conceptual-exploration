# Lean proofs of the order-2 rules

`Order2/Proofs.lean` proves in Lean the 26 rules of the reduced basis of [`results/order2_vampire_etp`](../results/order2_vampire_etp), the exploration of the ETP laws of order at most two. `Order2/Basic.lean` defines the laws as the ETP does, and `Order2/Superposition.lean` is the ETP's tactics, which check each step of a Vampire proof. Build with [Lean](https://lean-lang.org) 4.29.1, which `elan` installs from `lean-toolchain`:

```bash
lake build
```

Both files are written by `lean_proofs.py` from the exploration's log, the ETP's `equations.txt` and Vampire's proofs; `--prover9` also checks every rule with Prover9:

```bash
python explorations/equational_theories/lean_proofs.py equations.txt explorations/equational_theories/results/order2_vampire_etp/exploration.log -o explorations/equational_theories/lean --prover9
```
