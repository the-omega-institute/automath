import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

theorem paper_pom_diagonal_rate_critical_eigenvector_shape_sign_separation
    {n : ℕ} (t v : Fin n → ℝ) (lam σ : ℝ) (hσ : σ ≠ 0)
    (hshape : ∀ i, v i = σ / (t i - lam))
    (hsplit :
      ∃ k, (∀ i : Fin n, i.1 < k → t i < lam) ∧ (∀ i : Fin n, k ≤ i.1 → lam < t i)) :
    ∃ k, (∀ i : Fin n, i.1 < k → v i * σ < 0) ∧ (∀ i : Fin n, k ≤ i.1 → 0 < v i * σ) := by
  rcases hsplit with ⟨k, hk_left, hk_right⟩
  refine ⟨k, ?_, ?_⟩
  · intro i hi
    have hnum : 0 < σ ^ 2 := sq_pos_iff.mpr hσ
    have hden : t i - lam < 0 := sub_neg.mpr (hk_left i hi)
    have hrewrite : v i * σ = σ ^ 2 / (t i - lam) := by
      rw [hshape i, pow_two, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hrewrite]
    exact div_neg_of_pos_of_neg hnum hden
  · intro i hi
    have hnum : 0 < σ ^ 2 := sq_pos_iff.mpr hσ
    have hden : 0 < t i - lam := sub_pos.mpr (hk_right i hi)
    have hrewrite : v i * σ = σ ^ 2 / (t i - lam) := by
      rw [hshape i, pow_two, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hrewrite]
    exact div_pos hnum hden

end Omega.POM
