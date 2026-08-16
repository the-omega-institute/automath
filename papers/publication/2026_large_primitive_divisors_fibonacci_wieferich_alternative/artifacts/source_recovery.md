# Historical Source Recovery

The recovered source tree is commit
`c9c5bfe24d9a884294da8cdfab4cd7b1a39f35c1`, the parent of restructuring
commit `5231658ed`. Each file below was read with
`git show 5231658ed^:<path>`. Blob identifiers make the recovered inputs
auditable without modifying the companion working tree.

## Retained Material

| Historical file | Blob | Use in this article |
|---|---|---|
| `sec_large_primitive_divisor_alternative.tex` | `780b58b48d8d7c18198f161bb45c30771f8c9884` | Retained as the central primitive-part lemma, main alternative, conditional corollary within that theorem, and comparison with known large-divisor results. |
| `sec_rank_window_and_fibotomic_interface.tex` | `46185063ddebadceb1b7ab185c86916b77265099` | Retained only the coherent fibotomic integer, exact-rank radical, entropy inequality, weighted inequality, and pointwise exact-rank estimate. The rank-window deaggregation material was excluded. |

The article also restates and proves the classical rank congruence, valuation
equivalence, and exact-rank existence used by those recovered arguments. The
companion is cited for provenance, not used as an unstated proof input.

## Excluded Material

| Historical file | Blob | Reason for exclusion |
|---|---|---|
| `sec_support_entropy_arithmetic_interface.tex` | `18cfa3b5a31f03e73b73c086d1ea1f2c63a34400` | Concerns witness-cover counts and conditional rank-window hypotheses, not the primitive-divisor alternative. |
| `sec_prime_inverse_dynamics.tex` | `8fa2628a1ebce6cbe96ecca0b1cb91d674d640b3` | Gives inverse rays and fixed-point basins from classical exact-rank existence; it is independent of the fibotomic large-divisor argument. |
| `sec_further_questions.tex` | `0f36cfbde960c0c201d9d49d68a47f804b9c6dc1` | Asks about weighted witness covers and rank-window hypotheses, outside the retained arithmetic theorem. |
| `sec_arithmetic_secondary_bounds.tex` | `df5fbe9247add0518d4416f31f09a79ee28a4d26` | Bounds the residual witness-cover multiplicity and derives cover-count growth, not primitive divisor size. |
| `sec_connected_dominance_criterion.tex` | `86e6dd4e79bd24bd44bbae903e31998750608f08` | Develops connected dominance for witness covers, a separate combinatorial story. |
| `sec_connected_factorization.tex` | `5e4aa6efeee6b0609bfbb4812e889cf163dae3d9` | Factorizes birth layers and minimal generators over connected support blocks; unrelated to the main alternative. |
| `sec_connected_secondary_consequences.tex` | `3c59568af8ec66d494357088e7ee27b35a9d3155` | Gives inversion and four-support reductions downstream of connected factorization. |
| `sec_four_coordinate_classification.tex` | `474baf8e9b8c45de250f1323398dabc69bf98554` | Classifies four-coordinate witness kernels and arithmetic realizations, not exact-rank prime size. |
| `sec_low_support_classification.tex` | `c8d950bc90b63d6d7b6ca89c0f00292e7198875b` | Classifies three-coordinate families and obstruction certificates, a separate low-support paper. |
| `sec_low_support_framework.tex` | `03e7e2b45becc29246e94c4768ad99b33f0da150` | Supplies the prime/ladder framework for low-support classifications; the present article needs only a much smaller classical valuation statement, which it proves directly. |
| `sec_odd_layer_minimal_covers.tex` | `79c2dece3ee3da0dae2bcdde8cc68463cdb4c55d` | Realizes odd-layer minimal covers, wholly within the witness-cover program. |
| `sec_rank_pure_secondary_asymptotics.tex` | `b22a070162d66e7d667ce1022b2a6b2895b814e4` | Gives connected-cover concentration and local limits in a rank-pure sector, not the primitive-divisor theorem. |

The excluded files naturally divide into two other stories: prime inverse
dynamics, and the larger witness-cover/low-support/connected-factorization
program. Neither is needed for the pointwise primitive-divisor alternative,
so neither is assembled here.
