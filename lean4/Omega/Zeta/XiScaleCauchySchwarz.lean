import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `con:xi-scale-cauchy-schwarz`. -/
theorem paper_xi_scale_cauchy_schwarz {ι : Type} [Fintype ι] (w a : ι → ℝ) (t Φ : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hΦ : Φ = ∑ j, w j) (hden : ∀ j, 0 < t + a j) :
    (∑ j, w j / (t + a j)) ^ 2 ≤ Φ * (∑ j, w j / (t + a j) ^ 2) := by
  classical
  have hcs :
      (∑ j ∈ (Finset.univ : Finset ι), w j / (t + a j)) ^ 2 ≤
        (∑ j ∈ (Finset.univ : Finset ι), w j) *
          ∑ j ∈ (Finset.univ : Finset ι), w j / (t + a j) ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (s := (Finset.univ : Finset ι))
      (r := fun j => w j / (t + a j))
      (f := w)
      (g := fun j => w j / (t + a j) ^ 2)
      ?_ ?_ ?_
    · intro j _hj
      exact hw j
    · intro j _hj
      exact div_nonneg (hw j) (sq_nonneg (t + a j))
    · intro j _hj
      have hne : t + a j ≠ 0 := (hden j).ne'
      field_simp [hne]
  simpa [hΦ] using hcs

end Omega.Zeta
