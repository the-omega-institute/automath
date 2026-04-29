import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Conclusion.Window6BinarySuffixCylinderTrichotomy
import Omega.Conclusion.Window6Collision
import Omega.Conclusion.Window6OrdinaryBinaryStrictMajorization
import Omega.Conclusion.Window6OutputBlindChannelDominates
import Omega.Conclusion.Window6OutputChi2VisibleBlindOrthogonalSplitting
import Omega.Conclusion.Window6OutputKLExactGcdChainSplitting

namespace Omega.Conclusion

/-- The explicit suffix-cylinder decomposition of the binary `window-6` model. -/
def window6BinarySuffixCylinderTrichotomy : Prop :=
  window6BinaryLayer 2 = window6X4Suffix01 ∧
    window6BinaryLayer 3 = window6X3NonzeroSuffix010 ∧
    window6BinaryLayer 4 = window6X4Suffix00 ∪ {window6ExceptionalWord} ∧
    Disjoint window6X5Suffix0 window6X4Suffix01 ∧
    window6X5Suffix0 ∪ window6X4Suffix01 = window6All

/-- The ordinary histogram strictly majorizes the binary histogram. -/
def window6OrdinaryBinaryStrictMajorization : Prop :=
  let ord : List Nat := [5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1]
  let bin : List Nat := [4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]
  ord.sum = bin.sum ∧
    (∀ k : Nat, 1 ≤ k → k ≤ ord.length → (ord.take k).sum ≥ (bin.take k).sum) ∧
    (∃ k : Nat, 1 ≤ k ∧ k < ord.length ∧ (ord.take k).sum > (bin.take k).sum)

/-- The strict Schur certificate yields an explicit entropy gain, while the capacity curve saturates
at the full `64` visible microstates from scale `B = 2` onward. -/
def window6BinaryEntropyCapacityImprovement : Prop :=
  window6ExactGcdBlindKl = (1 / 4 : ℝ) * Real.log (32 / 27 : ℝ) ∧
    8 * min 2 (2 ^ 0) + 4 * min 3 (2 ^ 0) + 9 * min 4 (2 ^ 0) = 21 ∧
    8 * min 2 (2 ^ 1) + 4 * min 3 (2 ^ 1) + 9 * min 4 (2 ^ 1) = 42 ∧
    (∀ B : Nat, 2 ≤ B → 8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B) = 64)

/-- The visible/blind split exposes the exact blind-channel share and the reduced collision
constant. -/
def window6BinaryVisibleBitsCollisionDrop : Prop :=
  window6ExactGcdBlindChi2 / (window6ExactGcdVisibleChi2 + window6ExactGcdBlindChi2) =
      (84 / 89 : ℝ) ∧
    window6ExactGcdBlindKl / (window6ExactGcdVisibleKl + window6ExactGcdBlindKl) =
      ((1 / 4 : ℝ) * Real.log (32 / 27 : ℝ)) /
        ((15 / 16 : ℝ) * Real.log (63 / 64 : ℝ) +
          (1 / 16 : ℝ) * Real.log (21 / 16 : ℝ) +
          (1 / 4 : ℝ) * Real.log (32 / 27 : ℝ)) ∧
    212 * 1024 = 53 * 4096

/-- Paper label: `thm:conclusion-window6-binary-uplift-strict-schur-uniformizer`. -/
theorem paper_conclusion_window6_binary_uplift_strict_schur_uniformizer :
    window6BinarySuffixCylinderTrichotomy ∧ window6OrdinaryBinaryStrictMajorization ∧
      window6BinaryEntropyCapacityImprovement ∧ window6BinaryVisibleBitsCollisionDrop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact paper_conclusion_window6_binary_suffix_cylinder_trichotomy
  · exact paper_conclusion_window6_ordinary_binary_strict_majorization
  · rcases paper_conclusion_window6_output_kl_exact_gcd_chain_splitting with ⟨_, hBlindKl, _⟩
    rcases paper_conclusion_window6_continuous_capacity_piecewise_closed with ⟨hB0, hB1, hBge2⟩
    exact ⟨hBlindKl, hB0, hB1, hBge2⟩
  · rcases paper_conclusion_window6_output_blind_channel_dominates with ⟨hChi2, hKl⟩
    exact ⟨hChi2, hKl, paper_window6_collision_prob⟩

end Omega.Conclusion
