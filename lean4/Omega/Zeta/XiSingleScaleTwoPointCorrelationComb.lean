import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-single-scale-two-point-correlation-comb`. -/
theorem paper_xi_single_scale_two_point_correlation_comb {ι : Type*} [Fintype ι]
    (phase : ι → ℝ) : ∃ A : Finset ℝ, ∀ i j : ι, phase i - phase j ∈ A := by
  classical
  refine ⟨Finset.univ.image (fun p : ι × ι => phase p.1 - phase p.2), ?_⟩
  intro i j
  exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩

end Omega.Zeta
