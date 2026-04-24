import Mathlib

namespace Omega.OperatorAlgebra

/-- The critical-line point `1/2 + it`. -/
noncomputable def modularScatteringCriticalPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

private lemma one_sub_modularScatteringCriticalPoint (t : ℝ) :
    (1 : ℂ) - modularScatteringCriticalPoint t = star (modularScatteringCriticalPoint t) := by
  apply Complex.ext
  · simp [modularScatteringCriticalPoint]
    norm_num
  · simp [modularScatteringCriticalPoint]

/-- Paper label: `prop:op-algebra-modular-scattering-phase`.
If the scattering determinant satisfies the reciprocity law `φ(s) φ(1-s) = 1` and the critical-line
reflection identifies the opposite point with complex conjugation, then the determinant has unit
modulus on the critical slice. -/
theorem paper_op_algebra_modular_scattering_phase
    (φsc : ℂ → ℂ)
    (hrec : ∀ s : ℂ, φsc s * φsc (1 - s) = 1)
    (hcrit :
      ∀ t : ℝ,
        φsc (star (modularScatteringCriticalPoint t)) =
          star (φsc (modularScatteringCriticalPoint t))) :
    ∀ t : ℝ, ‖φsc (modularScatteringCriticalPoint t)‖ = 1 := by
  intro t
  let z := φsc (modularScatteringCriticalPoint t)
  have hmul : z * star z = 1 := by
    dsimp [z]
    calc
      φsc (modularScatteringCriticalPoint t) * star (φsc (modularScatteringCriticalPoint t)) =
          φsc (modularScatteringCriticalPoint t) *
            φsc (star (modularScatteringCriticalPoint t)) := by rw [hcrit t]
      _ = φsc (modularScatteringCriticalPoint t) * φsc (1 - modularScatteringCriticalPoint t) := by
        rw [one_sub_modularScatteringCriticalPoint]
      _ = 1 := hrec _
  have hnorm_mul : ‖z‖ * ‖star z‖ = 1 := by
    have := congrArg norm hmul
    simpa [norm_mul] using this
  have hsq : ‖z‖ ^ 2 = 1 := by
    simpa [pow_two, norm_star] using hnorm_mul
  have hnonneg : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith

end Omega.OperatorAlgebra
