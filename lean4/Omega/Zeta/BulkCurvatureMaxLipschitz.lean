import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-bulk-curvature-max-lipschitz`. A pointwise curvature bound and the
identity `v' = K` imply the corresponding global Lipschitz bound for the velocity. -/
theorem paper_xi_bulk_curvature_max_lipschitz
    (κ : ℕ) (hκ : 0 < κ) (K v : ℝ → ℝ) (hK_pos : ∀ s, 0 < K s)
    (hK_bound : ∀ s, K s ≤ ((((2 * κ - 1) * κ : ℕ) : ℝ) / 4))
    (hderiv : ∀ s, HasDerivAt v (K s) s) :
    (∀ s, 0 < K s ∧ K s ≤ ((((2 * κ - 1) * κ : ℕ) : ℝ) / 4)) ∧
      ∀ s1 s2,
        |v s2 - v s1| ≤
          ((((2 * κ - 1) * κ : ℕ) : ℝ) / 4) * |s2 - s1| := by
  classical
  have _hκ_used : 0 < κ := hκ
  let C : ℝ := ((((2 * κ - 1) * κ : ℕ) : ℝ) / 4)
  have hpoint : ∀ s, 0 < K s ∧ K s ≤ C := fun s => ⟨hK_pos s, hK_bound s⟩
  refine ⟨hpoint, ?_⟩
  intro s1 s2
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ v x := by
    intro x _hx
    exact (hderiv x).differentiableAt
  have hbound : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv v x‖ ≤ C := by
    intro x _hx
    rw [(hderiv x).deriv]
    simpa [Real.norm_eq_abs, abs_of_pos (hK_pos x), C] using hK_bound x
  have hmvt :=
    convex_univ.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := (Set.univ : Set ℝ))
      (f := v) (x := s1) (y := s2) hdiff hbound (by simp) (by simp)
  simpa [Real.norm_eq_abs, C] using hmvt

end Omega.Zeta
