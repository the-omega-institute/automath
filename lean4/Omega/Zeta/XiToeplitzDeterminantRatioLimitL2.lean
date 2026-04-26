import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Omega.Zeta.XiToeplitzCurvatureEnergyEquivalence

namespace Omega.Zeta

open XiToeplitzDetVerblunskyData

noncomputable section

lemma xi_toeplitz_determinant_ratio_limit_l2_stepFactor_tail
    (D : XiToeplitzDetVerblunskyData) (n : ℕ) :
    D.stepFactor (n + D.steps) = 1 := by
  unfold XiToeplitzDetVerblunskyData.stepFactor XiToeplitzDetVerblunskyData.alphaAt
  have hnot : ¬ n + D.steps < D.steps := by omega
  simp [hnot]

lemma xi_toeplitz_determinant_ratio_limit_l2_toeplitzDet_tail
    (D : XiToeplitzDetVerblunskyData) :
    ∀ n : ℕ, D.toeplitzDet (n + D.steps) = D.toeplitzDet D.steps
  | 0 => by simp
  | n + 1 => by
      rw [Nat.succ_add, XiToeplitzDetVerblunskyData.toeplitzDet,
        xi_toeplitz_determinant_ratio_limit_l2_stepFactor_tail,
        mul_one, xi_toeplitz_determinant_ratio_limit_l2_toeplitzDet_tail D n]

/-- Paper label: `prop:xi-toeplitz-determinant-ratio-limit-l2`. -/
theorem paper_xi_toeplitz_determinant_ratio_limit_l2 (D : Omega.Zeta.XiToeplitzDetVerblunskyData)
    (hgood : ∀ n < D.steps, |D.alphaAt n| < 1) :
    (∃ rInf > 0, ∀ n : ℕ, D.toeplitzDet (n + D.steps + 1) / D.toeplitzDet (n + D.steps) = rInf) ∧
      (Summable (fun n : ℕ => |D.alphaAt n| ^ (2 : ℕ)) ↔
        ∃ rInf > 0, ∀ n : ℕ, D.toeplitzDet (n + D.steps + 1) / D.toeplitzDet (n + D.steps) = rInf) := by
  have htail :
      ∀ n : ℕ, D.toeplitzDet (n + D.steps + 1) / D.toeplitzDet (n + D.steps) = 1 := by
    intro n
    have hnum : D.toeplitzDet (n + D.steps + 1) = D.toeplitzDet D.steps := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        xi_toeplitz_determinant_ratio_limit_l2_toeplitzDet_tail D (n + 1)
    have hden : D.toeplitzDet (n + D.steps) = D.toeplitzDet D.steps := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        xi_toeplitz_determinant_ratio_limit_l2_toeplitzDet_tail D n
    rw [hnum, hden]
    have hpos : 0 < D.toeplitzDet D.steps := by
      exact D.toeplitzDet_pos_of_prefix_good hgood
    field_simp [ne_of_gt hpos]
  have hexists :
      ∃ rInf > 0, ∀ n : ℕ, D.toeplitzDet (n + D.steps + 1) / D.toeplitzDet (n + D.steps) = rInf := by
    refine ⟨1, zero_lt_one, ?_⟩
    exact htail
  have hsummable : Summable (fun n : ℕ => D.alphaAt n ^ (2 : ℕ)) := by
    have hsummable0 :
        Summable (xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D) :=
      xi_toeplitz_curvature_energy_equivalence_reflectionEnergy_summable D
    have hfun :
        (fun n : ℕ => D.alphaAt n ^ (2 : ℕ)) =
          xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D := by
      funext n
      simp [xi_toeplitz_curvature_energy_equivalence_reflectionEnergy, sq_abs]
    rw [hfun]
    exact hsummable0
  refine ⟨hexists, ?_⟩
  constructor
  · intro _
    exact hexists
  · intro _
    simpa [sq_abs] using hsummable

end

end Omega.Zeta
