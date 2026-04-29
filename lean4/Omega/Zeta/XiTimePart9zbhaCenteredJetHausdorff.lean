import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-time-part9zbha-centered-jet-hausdorff`.  A finite atomic
Hausdorff representation supported in `[0,u0⁻¹]` has nonnegative moments, Hankel
quadratic forms, and localizing quadratic forms. -/
theorem paper_xi_time_part9zbha_centered_jet_hausdorff {Γ : Type*} [Fintype Γ] (u0 : ℝ)
    (w x : Γ → ℝ) (m : ℕ → ℝ) (hu0 : 0 < u0) (hw : ∀ γ, 0 ≤ w γ)
    (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ ≤ u0⁻¹)
    (hm : ∀ n, m n = ∑ γ, w γ * x γ ^ n) :
    (∀ n, 0 ≤ m n) ∧
      (∀ k (c : Fin (k + 1) → ℝ),
        0 ≤ ∑ i, ∑ j, c i * c j * m ((i : ℕ) + (j : ℕ))) ∧
      (∀ k (c : Fin (k + 1) → ℝ),
        0 ≤
          ∑ i, ∑ j,
            c i * c j * (u0⁻¹ * m ((i : ℕ) + (j : ℕ)) -
              m ((i : ℕ) + (j : ℕ) + 1))) := by
  classical
  have hu0_inv_nonneg : 0 ≤ u0⁻¹ := inv_nonneg.mpr hu0.le
  have weighted_square_identity :
      ∀ (v : Γ → ℝ) (q : ℕ → ℝ), (∀ n, q n = ∑ γ, v γ * x γ ^ n) →
        ∀ k (c : Fin (k + 1) → ℝ),
          (∑ i, ∑ j, c i * c j * q ((i : ℕ) + (j : ℕ))) =
            ∑ γ, v γ * (∑ i : Fin (k + 1), c i * x γ ^ (i : ℕ)) ^ 2 := by
    intro v q hq k c
    simp_rw [hq, pow_add, Finset.mul_sum]
    conv_lhs =>
      rw [← Finset.sum_product']
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    rw [Finset.sum_product]
    simp [sq, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [hm n]
    exact Finset.sum_nonneg fun γ _ => mul_nonneg (hw γ) (pow_nonneg (hx0 γ) n)
  · intro k c
    have hsq :=
      weighted_square_identity w m hm k c
    rw [hsq]
    exact Finset.sum_nonneg fun γ _ => mul_nonneg (hw γ) (sq_nonneg _)
  · intro k c
    have hlocal_moment :
        ∀ n, u0⁻¹ * m n - m (n + 1) =
          ∑ γ, (w γ * (u0⁻¹ - x γ)) * x γ ^ n := by
      intro n
      rw [hm n, hm (n + 1)]
      calc
        u0⁻¹ * (∑ γ, w γ * x γ ^ n) - ∑ γ, w γ * x γ ^ (n + 1) =
            ∑ γ, (u0⁻¹ * (w γ * x γ ^ n) - w γ * x γ ^ (n + 1)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        _ = ∑ γ, (w γ * (u0⁻¹ - x γ)) * x γ ^ n := by
          apply Finset.sum_congr rfl
          intro γ _
          rw [pow_succ']
          ring
    have hsq :=
      weighted_square_identity (fun γ => w γ * (u0⁻¹ - x γ))
        (fun n => u0⁻¹ * m n - m (n + 1)) hlocal_moment k c
    rw [hsq]
    exact
      Finset.sum_nonneg fun γ _ => by
        have hfactor : 0 ≤ u0⁻¹ - x γ := by linarith [hu0_inv_nonneg, hx1 γ]
        exact mul_nonneg (mul_nonneg (hw γ) hfactor) (sq_nonneg _)

end Omega.Zeta
