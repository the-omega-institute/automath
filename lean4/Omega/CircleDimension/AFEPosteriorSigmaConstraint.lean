import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

theorem paper_cdim_afe_posterior_sigma_constraint (sigma L A B eta deltaChi : ℝ) (hL : 0 < L)
    (hA : 0 < A) (hB : 0 < B) (heta : 0 < eta ∧ eta < 1)
    (hbound :
      |Real.log A - Real.log B + (sigma - 1 / 2) * L + deltaChi| ≤
        Real.log ((1 + eta) / (1 - eta))) :
    |(sigma - 1 / 2) + (Real.log A - Real.log B) / L| ≤
      Real.log ((1 + eta) / (1 - eta)) / L + |deltaChi| / L := by
  let err := Real.log A - Real.log B + (sigma - 1 / 2) * L
  let bound := Real.log ((1 + eta) / (1 - eta))
  have herr : |err| ≤ bound + |deltaChi| := by
    calc
      |err| = |(err + deltaChi) + (-deltaChi)| := by simp [err]
      _ ≤ |err + deltaChi| + |-deltaChi| := abs_add_le _ _
      _ = |err + deltaChi| + |deltaChi| := by simp
      _ ≤ bound + |deltaChi| := add_le_add hbound le_rfl
  have hrewrite : err / L = (sigma - 1 / 2) + (Real.log A - Real.log B) / L := by
    field_simp [err, hL.ne']
    ring
  calc
    |(sigma - 1 / 2) + (Real.log A - Real.log B) / L| = |err / L| := by rw [← hrewrite]
    _ = |err| / L := by rw [abs_div, abs_of_pos hL]
    _ ≤ (bound + |deltaChi|) / L := div_le_div_of_nonneg_right herr (le_of_lt hL)
    _ = bound / L + |deltaChi| / L := by rw [add_div]

end Omega.CircleDimension
