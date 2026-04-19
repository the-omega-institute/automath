import Mathlib.Tactic
import Omega.GU.Window6B3C3SphericalCubatureStrength5

namespace Omega.GU

/-- Paper-facing normalized positive cone for the degree-`5` labeled spherical cubature family:
the total mass condition fixes `λ = 1 / 15`, so positivity becomes three independent interval
constraints on the transfer parameters. -/
theorem paper_window6_labeled_spherical_degree5_cubature_cube (lam t₁ t₂ t₃ : ℝ) :
    15 * lam = 1 →
      (((0 ≤ t₁ ∧ t₁ ≤ lam / 2) ∧ (0 ≤ t₂ ∧ t₂ ≤ lam / 2) ∧ (0 ≤ t₃ ∧ t₃ ≤ lam / 2)) ↔
        (lam = 1 / 15 ∧ (0 ≤ t₁ ∧ t₁ ≤ 1 / 30) ∧ (0 ≤ t₂ ∧ t₂ ≤ 1 / 30) ∧
          (0 ≤ t₃ ∧ t₃ ≤ 1 / 30))) := by
  intro hmass
  have hlam : lam = 1 / 15 := by
    nlinarith
  have hhalf : lam / 2 = 1 / 30 := by
    nlinarith [hlam]
  constructor
  · rintro ⟨ht₁, ht₂, ht₃⟩
    refine ⟨hlam, ?_, ?_, ?_⟩
    · simpa [hhalf] using ht₁
    · simpa [hhalf] using ht₂
    · simpa [hhalf] using ht₃
  · rintro ⟨hlam', ht₁, ht₂, ht₃⟩
    subst hlam'
    have hhalf' : (1 / 30 : ℝ) = (1 / 15 : ℝ) / 2 := by norm_num
    refine ⟨?_, ?_, ?_⟩
    · simpa [hhalf'] using ht₁
    · simpa [hhalf'] using ht₂
    · simpa [hhalf'] using ht₃

end Omega.GU
