# Verificação

Requer Python 3.12+, Lean 4.32.2, mathlib `905b95818eb32af7874a58b427f50c1711a5e96c` e WolframScript 15 licenciado. O Python utiliza a biblioteca padrão.

Com a versão fixada do conjunto de ferramentas do Lean no PATH:

```sh
git clone https://github.com/leanprover-community/mathlib4.git ../mathlib4
git -C ../mathlib4 checkout 905b95818eb32af7874a58b427f50c1711a5e96c
(cd ../mathlib4 && lake exe cache get)
python3 -B verify.py --all --output ../verification-results --lean-workspace ../mathlib4 --lean-bin "$(lean --print-prefix)/bin/lean"
```

Os arquivos de saída permanecem fora deste repositório de quatro arquivos. Em caso de falha, o comando retorna um código de saída diferente de zero. Omita `--all` para executar apenas a verificação em Python; use `--lean` ou `--wolfram` individualmente.

O Lean abrange os enunciados dos resultados matemáticos ao longo de todo o artigo. `RematUniformFinite.uniform_full_representation` demonstra o Teorema 1; `RematReciprocalCutoff.finite_reciprocal_realization` constrói a testemunha de corte/recíproco do Corolário 1; `RematIntervalTransfer.compact_no_interval_loss` demonstra sua obstrução. As demais provas não precisam reproduzir literalmente todas as construções descritas no texto. A compilação, as auditorias transitivas de axiomas e uma nova verificação por um kernel compatível aceitam apenas `propext`, `Classical.choice` e `Quot.sound`.

O Python testa perfis finitos, todos os vetores minimizadores nas grades testadas e derivadas de corte amostradas. O Wolfram verifica identidades simbólicas e limites. Essas verificações complementam as provas formais; nem os testes finitos nem a verificação de provas certificam a originalidade ou a aplicabilidade empírica.

Não são necessários dados de entrada privados nem conjuntos de dados.

# Verification (en)

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
