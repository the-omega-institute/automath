import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-pick-poisson-characteristic-zero-set-scaling`. -/
theorem paper_xi_pick_poisson_characteristic_zero_set_scaling (Psi : ℂ → ℝ → ℂ)
    (hhom : ∀ z m, 0 < m → Psi z m = Psi (z / (m : ℂ)) 1) :
    ∀ m, 0 < m →
      {z : ℂ | Psi z m = 0} =
        (fun z : ℂ => (m : ℂ) * z) '' {z : ℂ | Psi z 1 = 0} := by
  intro m hm
  ext z
  constructor
  · intro hz
    refine ⟨z / (m : ℂ), ?_, ?_⟩
    · simpa [hhom z m hm] using hz
    · have hm_ne : (m : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hm)
      field_simp [hm_ne]
  · rintro ⟨w, hw, rfl⟩
    have hm_ne : (m : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hm)
    simpa [hhom ((m : ℂ) * w) m hm, hm_ne] using hw

end Omega.Zeta
