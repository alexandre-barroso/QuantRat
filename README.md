# Verification

Requires Python 3.12+, Lean 4.32.2, mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`, and licensed WolframScript 15. Python uses the standard library.

With the pinned Lean toolchain on PATH:

```sh
git clone https://github.com/leanprover-community/mathlib4.git ../mathlib4
git -C ../mathlib4 checkout 905b95818eb32af7874a58b427f50c1711a5e96c
(cd ../mathlib4 && lake exe cache get)
python3 -B verify.py --all --output ../verification-results --lean-workspace ../mathlib4 --lean-bin "$(lean --print-prefix)/bin/lean"
```

Outputs stay outside this four-file repository. Failures return nonzero. Omit `--all` for Python alone; use `--lean` or `--wolfram` individually.

Lean covers the mathematical result statements throughout the paper. `RematUniformFinite.uniform_full_representation` proves Theorem 1; `RematReciprocalCutoff.finite_reciprocal_realization` constructs Corollary 1's cutoff/reciprocal witness; `RematIntervalTransfer.compact_no_interval_loss` proves its obstruction. Other proofs need not reproduce every written construction literally. Compilation, transitive axiom audits and fresh compatible-kernel replay accept only `propext`, `Classical.choice`, and `Quot.sound`.

Python tests finite profiles, every minimizing vector on tested grids, and sampled cutoff derivatives. Wolfram checks symbolic identities and limits. These complement the formal proofs; neither finite tests nor proof checking certify novelty or empirical applicability.

No private inputs or datasets are required.
