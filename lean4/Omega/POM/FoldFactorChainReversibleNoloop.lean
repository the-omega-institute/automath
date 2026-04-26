import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- The concrete compressed fold-factor chain used in the reversible/no-loop package. -/
def pom_fold_factor_chain_reversible_noloop_kernel : Fin 2 → Fin 2 → ℚ
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => 0

/-- Uniform lift of the stationary law on the two-state compressed chain. -/
def pom_fold_factor_chain_reversible_noloop_stationary : Fin 2 → ℚ :=
  fun _ => 1 / 2

/-- Chapter-local package: the uniform lift is stationary for the compressed chain, the chain
satisfies detailed balance with respect to that law, and the diagonal vanishes. -/
def pom_fold_factor_chain_reversible_noloop_statement : Prop :=
  (∀ i : Fin 2,
    (∑ j : Fin 2,
        pom_fold_factor_chain_reversible_noloop_stationary j *
          pom_fold_factor_chain_reversible_noloop_kernel j i) =
      pom_fold_factor_chain_reversible_noloop_stationary i) ∧
    (∀ i j : Fin 2,
      pom_fold_factor_chain_reversible_noloop_stationary i *
          pom_fold_factor_chain_reversible_noloop_kernel i j =
        pom_fold_factor_chain_reversible_noloop_stationary j *
          pom_fold_factor_chain_reversible_noloop_kernel j i) ∧
    (∀ i : Fin 2, pom_fold_factor_chain_reversible_noloop_kernel i i = 0)

/-- Paper label: `prop:pom-fold-factor-chain-reversible-noloop`. -/
theorem paper_pom_fold_factor_chain_reversible_noloop :
    pom_fold_factor_chain_reversible_noloop_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [pom_fold_factor_chain_reversible_noloop_stationary,
      pom_fold_factor_chain_reversible_noloop_kernel]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [pom_fold_factor_chain_reversible_noloop_stationary,
      pom_fold_factor_chain_reversible_noloop_kernel]
  · intro i
    fin_cases i <;> norm_num [pom_fold_factor_chain_reversible_noloop_kernel]

end Omega.POM
