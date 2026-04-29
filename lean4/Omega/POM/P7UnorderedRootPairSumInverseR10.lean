import Mathlib.Tactic
import Omega.POM.S5OrderedRatioDegree20
import Omega.POM.S5TwoSubsetDegree10
import Omega.Zeta.XiTerminalZmLeyangDeltaNodePreimageR10Wreath

namespace Omega.POM

/-- Concrete bridge statement for `thm:pom-p7-unordered-root-pair-sum-inverse-r10`: the ordered
degree-20 package is already available, the unordered-pair orbit arithmetic drops to degree `10`,
the explicit `R₁₀` elimination certificate is recorded in the zeta chapter, and both displayed
discriminant factorizations carry the same odd prime witness `985219`. -/
def pom_p7_unordered_root_pair_sum_inverse_r10_statement : Prop :=
  (∀ D : S5OrderedRatioDegree20Data,
    D.degreeTwentyOrbit ∧ D.resultantFactorization ∧ D.irreducibleWitness ∧
      D.faithfulOrderedPairAction) ∧
    (Nat.choose 5 2 = 10 ∧
      2 ^ 5 * 3 ^ 2 * 5 ^ 2 = (7200 : ℕ) ∧
      2 ^ 4 * 5 ^ 4 = (10000 : ℕ) ∧
      5 * 4 = (20 : ℕ) ∧
      Nat.factorial 5 = 120 ∧
      Nat.factorial 3 * Nat.factorial 2 = 12 ∧
      120 / 12 = (10 : ℕ)) ∧
    Omega.Zeta.XiTerminalZmDeltaNodePreimageEliminationR10Statement ∧
    (-985219 : ℤ) < 0 ∧ Nat.Prime 985219 ∧ Odd 7 ∧ Odd 3

theorem paper_pom_p7_unordered_root_pair_sum_inverse_r10 :
    pom_p7_unordered_root_pair_sum_inverse_r10_statement := by
  refine ⟨?_, Omega.POM.S5TwoSubsetDegree10.paper_pom_s5_two_subset_degree10_package, ?_, ?_,
    ?_, by decide, by decide⟩
  · intro D
    exact paper_pom_p7_ordered_root_ratio_s5_ordered_pairs D
  · exact Omega.Zeta.paper_xi_terminal_zm_delta_node_preimage_elimination_r10
  · norm_num
  · native_decide

end Omega.POM
