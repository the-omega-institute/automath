import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The pressure profile `P(θ) = log λ(e^θ)`. -/
noncomputable def gcPressure (lam : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.log (lam (Real.exp θ))

/-- The centered cumulant generator `Λ(θ) = P(θ) - θ / 2`. -/
noncomputable def gcCenteredCgf (lam : ℝ → ℝ) (θ : ℝ) : ℝ :=
  gcPressure lam θ - θ / 2

/-- Gallavotti-Cohen symmetry written directly at the pressure level. -/
def gcPressureDuality (lam : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, gcPressure lam θ = θ + gcPressure lam (-θ)

/-- Vanishing odd part of the centered cumulant generator. -/
def gcOddPartVanishes (lam : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, gcCenteredCgf lam θ - gcCenteredCgf lam (-θ) = 0

lemma gcPressure_duality_of_selfDual (lam : ℝ → ℝ)
    (hSelfDual : ∀ u > 0, lam u = u * lam (1 / u))
    (hPos : ∀ θ : ℝ, 0 < lam (Real.exp θ)) :
    gcPressureDuality lam := by
  intro θ
  calc
    gcPressure lam θ = Real.log (Real.exp θ * lam (Real.exp (-θ))) := by
      rw [gcPressure, hSelfDual (Real.exp θ) (Real.exp_pos θ)]
      simp [one_div, Real.exp_neg]
    _ = Real.log (Real.exp θ) + Real.log (lam (Real.exp (-θ))) := by
      have hexp0 : Real.exp θ ≠ 0 := ne_of_gt (Real.exp_pos θ)
      have hlam0 : lam (Real.exp (-θ)) ≠ 0 := ne_of_gt (hPos (-θ))
      rw [Real.log_mul hexp0 hlam0]
    _ = θ + gcPressure lam (-θ) := by
      simp [gcPressure]

lemma gcCentered_even (lam : ℝ → ℝ)
    (hSelfDual : ∀ u > 0, lam u = u * lam (1 / u))
    (hPos : ∀ θ : ℝ, 0 < lam (Real.exp θ)) :
    ∀ θ : ℝ, gcCenteredCgf lam θ = gcCenteredCgf lam (-θ) := by
  intro θ
  have hDual := gcPressure_duality_of_selfDual lam hSelfDual hPos θ
  calc
    gcCenteredCgf lam θ = gcPressure lam θ - θ / 2 := rfl
    _ = gcPressure lam (-θ) + θ / 2 := by
      rw [hDual]
      ring
    _ = gcCenteredCgf lam (-θ) := by
      simp [gcCenteredCgf]
      ring

/-- The self-duality relation `λ(u) = u λ(1/u)` becomes an even centered cumulant generator on
the logarithmic coordinate, and hence its odd part vanishes identically.
    thm:sync-kernel-gallavotti-cohen -/
theorem paper_sync_kernel_gallavotti_cohen
    (lam : ℝ → ℝ)
    (hSelfDual : ∀ u > 0, lam u = u * lam (1 / u))
    (hPos : ∀ θ : ℝ, 0 < lam (Real.exp θ)) :
    gcPressureDuality lam ∧
      (∀ θ : ℝ, gcCenteredCgf lam θ = gcCenteredCgf lam (-θ)) ∧
      gcOddPartVanishes lam := by
  refine ⟨gcPressure_duality_of_selfDual lam hSelfDual hPos, gcCentered_even lam hSelfDual hPos, ?_⟩
  intro θ
  rw [gcCentered_even lam hSelfDual hPos θ]
  ring

end Omega.SyncKernelWeighted
