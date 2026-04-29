import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-offslice-near-critical-stability`. -/
theorem paper_xi_offslice_near_critical_stability {ι : Type*} [Fintype ι]
    (rePart : ι → ℝ) (L ε W : ℝ) (hL : 0 < L) (hW : W ≤ ε)
    (hdev_nonneg : ∀ z, 0 ≤ rePart z - (1 / 2 : ℝ))
    (hsum : (∑ z, rePart z - (1 / 2 : ℝ)) = W / (2 * L)) :
    (∀ z, rePart z - (1 / 2 : ℝ) ≤ ε / (2 * L)) ∧
      (∑ z, rePart z - (1 / 2 : ℝ)) ≤ ε / (2 * L) := by
  have hden_pos : 0 < 2 * L := by nlinarith
  have htotal_le : (∑ z, rePart z - (1 / 2 : ℝ)) ≤ ε / (2 * L) := by
    rw [hsum]
    exact div_le_div_of_nonneg_right hW hden_pos.le
  refine ⟨?_, htotal_le⟩
  intro z
  have hre_nonneg : ∀ y, 0 ≤ rePart y := by
    intro y
    have := hdev_nonneg y
    linarith
  have hsingle_le_sum : rePart z ≤ ∑ y, rePart y := by
    exact
      Finset.single_le_sum (s := Finset.univ) (a := z) (f := rePart)
        (fun y _ => hre_nonneg y) (Finset.mem_univ z)
  linarith

end Omega.Zeta
