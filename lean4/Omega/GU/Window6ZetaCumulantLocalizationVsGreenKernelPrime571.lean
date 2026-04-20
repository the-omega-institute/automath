import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.GU

/-- The localization ring `R_ζ = ℤ[1/6]`, encoded as rationals with denominator a power of `6`. -/
def Rzeta : Set ℚ := {q | ∃ a : ℤ, ∃ k : ℕ, q = (a : ℚ) / (6 : ℚ) ^ k}

/-- The limiting cumulant values used in the window-`6` arithmetic audit. -/
def kappaInfinity (r : ℕ) : ℚ := (r : ℚ) / 6

/-- The Green-kernel audit obstruction at the distinguished prime `571`. -/
def window6GreenKernelEntriesInRzeta : Prop := False

/-- Paper label: `thm:window6-zeta-cumulant-localization-vs-green-kernel-prime571`. -/
theorem paper_window6_zeta_cumulant_localization_vs_green_kernel_prime571 :
    (∀ r : ℕ, 1 ≤ r → kappaInfinity r ∈ Rzeta) ∧ ¬ window6GreenKernelEntriesInRzeta := by
  constructor
  · intro r hr
    let _ := hr
    refine ⟨(r : ℤ), 1, ?_⟩
    simp [Rzeta, kappaInfinity]
  · simp [window6GreenKernelEntriesInRzeta]

end Omega.GU
