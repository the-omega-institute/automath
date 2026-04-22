import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

theorem paper_finite_rh_phase_lift_time_rescale (q : ℕ) (liftDet detPow liftZeta zetaPow : ℂ → ℂ)
    (hdet : ∀ z : ℂ, liftDet z = detPow (z ^ q))
    (hlift : ∀ z : ℂ, liftDet z ≠ 0 → liftZeta z = (liftDet z)⁻¹)
    (hpow : ∀ z : ℂ, detPow (z ^ q) ≠ 0 → zetaPow (z ^ q) = (detPow (z ^ q))⁻¹) :
    ∀ z : ℂ, liftDet z = detPow (z ^ q) ∧ (liftDet z ≠ 0 → liftZeta z = zetaPow (z ^ q)) := by
  intro z
  refine ⟨hdet z, ?_⟩
  intro hz
  rw [hlift z hz, hpow z]
  · rw [← hdet z]
  · simpa [hdet z] using hz

end Omega.Zeta
