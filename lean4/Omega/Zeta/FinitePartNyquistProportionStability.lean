import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:finite-part-nyquist-proportion-stability`. -/
theorem paper_finite_part_nyquist_proportion_stability
    (sampleEnergy : ℕ → ℝ) (E K Λ : ℝ) (hE : 0 < E)
    (h : ∀ q : ℕ, 1 ≤ q → |sampleEnergy q / E - 1| ≤ K / E * Λ ^ q) :
    (∀ q : ℕ, 1 ≤ q → |sampleEnergy q / E - 1| ≤ K / E * Λ ^ q) ∧
      ∀ q₁ q₂ : ℕ, 1 ≤ q₁ → 1 ≤ q₂ →
        |sampleEnergy q₁ / E - sampleEnergy q₂ / E| ≤ K / E * (Λ ^ q₁ + Λ ^ q₂) := by
  have _hE_ne : E ≠ 0 := ne_of_gt hE
  refine ⟨h, ?_⟩
  intro q₁ q₂ hq₁ hq₂
  have htri :
      |sampleEnergy q₁ / E - sampleEnergy q₂ / E| ≤
        |sampleEnergy q₁ / E - 1| + |sampleEnergy q₂ / E - 1| := by
    simpa [abs_sub_comm]
      using abs_sub_le (sampleEnergy q₁ / E) 1 (sampleEnergy q₂ / E)
  calc
    |sampleEnergy q₁ / E - sampleEnergy q₂ / E|
        ≤ |sampleEnergy q₁ / E - 1| + |sampleEnergy q₂ / E - 1| := htri
    _ ≤ K / E * Λ ^ q₁ + K / E * Λ ^ q₂ := add_le_add (h q₁ hq₁) (h q₂ hq₂)
    _ = K / E * (Λ ^ q₁ + Λ ^ q₂) := by ring

end Omega.Zeta
