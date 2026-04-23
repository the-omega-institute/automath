import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `prop:xi-rankone-secular-monotonicity-derivative-norm`. -/
theorem paper_xi_rankone_secular_monotonicity_derivative_norm {q : Nat}
    (t w : Fin (q + 1) → Real) (b lambda dlambda : Real) (hw : ∀ i, 0 < w i) (hb : 0 < b)
    (hsecular : (∑ i, w i / (lambda - t i)) = 1 / b)
    (hderiv : dlambda = 1 / (b^2 * ∑ i, w i / (lambda - t i)^2)) :
    0 < dlambda ∧ (∑ i, w i / (lambda - t i)^2) = 1 / (b^2 * dlambda) := by
  let s : Real := ∑ i, w i / (lambda - t i)^2
  have hterm_nonneg : ∀ i, 0 ≤ w i / (lambda - t i)^2 := by
    intro i
    exact div_nonneg (le_of_lt (hw i)) (sq_nonneg _)
  have hs_pos : 0 < s := by
    have hsome : ∃ i, lambda - t i ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      have hsum_zero : (∑ i, w i / (lambda - t i)) = 0 := by
        simp [hnone]
      have hsum_pos : 0 < ∑ i, w i / (lambda - t i) := by
        rw [hsecular]
        exact one_div_pos.mpr hb
      linarith
    rcases hsome with ⟨i0, hi0⟩
    have hi0_pos : 0 < w i0 / (lambda - t i0)^2 := by
      exact div_pos (hw i0) (sq_pos_of_ne_zero hi0)
    have hi0_le : w i0 / (lambda - t i0)^2 ≤ s := by
      dsimp [s]
      exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (by simp)
    exact lt_of_lt_of_le hi0_pos hi0_le
  have hb_sq_pos : 0 < b ^ 2 := by nlinarith [hb]
  have hprod_pos : 0 < b ^ 2 * s := mul_pos hb_sq_pos hs_pos
  have hdlambda_pos : 0 < dlambda := by
    rw [hderiv]
    exact one_div_pos.mpr hprod_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hnorm : s = 1 / (b ^ 2 * dlambda) := by
    rw [hderiv]
    field_simp [hb_ne, hs_ne]
    ring
  exact ⟨hdlambda_pos, by simpa [s] using hnorm⟩

end Omega.Zeta
