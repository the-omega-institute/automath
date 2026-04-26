import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:derived-oracle-thermal-differential-geometry`.
This concrete wrapper records the algebraic implicit-differentiation step that remains after the
thermal-cut identity and slope readout have reduced the geometry to the relation
`Γ'(a) = 1 - q_*(a)`. The composed second/third `τ`-derivatives are treated as functions of the
energy parameter `a`. -/
def derived_oracle_thermal_differential_geometry_statement : Prop :=
  ∀ (qStar gammaPrime gammaSecond gammaThird tauSecondAlong tauThirdAlong qStarPrime qStarSecond :
      ℝ → ℝ) (a0 a1 : ℝ),
    (∀ a, gammaPrime a = 1 - qStar a) →
    (∀ a, a0 < a → a < a1 → gammaSecond a = -qStarPrime a) →
    (∀ a, a0 < a → a < a1 → tauSecondAlong a * qStarPrime a = 1) →
    (∀ a, a0 < a → a < a1 →
      qStarSecond a = -(tauThirdAlong a * qStarPrime a) / (tauSecondAlong a) ^ 2) →
    (∀ a, a0 < a → a < a1 → gammaThird a = -qStarSecond a) →
    qStar a0 = 0 →
    qStar a1 = 1 →
    (∀ a, a0 < a → a < a1 →
      gammaPrime a = 1 - qStar a ∧
        gammaSecond a = -(1 / tauSecondAlong a) ∧
        gammaThird a = tauThirdAlong a / (tauSecondAlong a) ^ 3) ∧
      gammaPrime a0 = 1 ∧
      gammaPrime a1 = 0

theorem paper_derived_oracle_thermal_differential_geometry :
    derived_oracle_thermal_differential_geometry_statement := by
  intro qStar gammaPrime gammaSecond gammaThird tauSecondAlong tauThirdAlong qStarPrime
    qStarSecond a0 a1 hSlope hSecond hImplicit hQSecond hThird hLeft hRight
  refine ⟨?_, ?_, ?_⟩
  · intro a ha0 ha1
    refine ⟨hSlope a, ?_, ?_⟩
    · have hImplicit_a := hImplicit a ha0 ha1
      have hTau_ne : tauSecondAlong a ≠ 0 := by
        intro hZero
        rw [hZero, zero_mul] at hImplicit_a
        norm_num at hImplicit_a
      have hQPrime :
          qStarPrime a = 1 / tauSecondAlong a := by
        apply (eq_div_iff hTau_ne).2
        simpa [mul_comm] using hImplicit_a
      calc
        gammaSecond a = -qStarPrime a := hSecond a ha0 ha1
        _ = -(1 / tauSecondAlong a) := by rw [hQPrime]
    · have hImplicit_a := hImplicit a ha0 ha1
      have hTau_ne : tauSecondAlong a ≠ 0 := by
        intro hZero
        rw [hZero, zero_mul] at hImplicit_a
        norm_num at hImplicit_a
      have hQPrime :
          qStarPrime a = 1 / tauSecondAlong a := by
        apply (eq_div_iff hTau_ne).2
        simpa [mul_comm] using hImplicit_a
      calc
        gammaThird a = -qStarSecond a := hThird a ha0 ha1
        _ = - (-(tauThirdAlong a * qStarPrime a) / (tauSecondAlong a) ^ 2) := by
              rw [hQSecond a ha0 ha1]
        _ = (tauThirdAlong a * qStarPrime a) / (tauSecondAlong a) ^ 2 := by ring
        _ = (tauThirdAlong a * (1 / tauSecondAlong a)) / (tauSecondAlong a) ^ 2 := by
              rw [hQPrime]
        _ = tauThirdAlong a / (tauSecondAlong a) ^ 3 := by
              field_simp [hTau_ne]
  · calc
      gammaPrime a0 = 1 - qStar a0 := hSlope a0
      _ = 1 := by rw [hLeft]; ring
  · calc
      gammaPrime a1 = 1 - qStar a1 := hSlope a1
      _ = 0 := by rw [hRight]; ring

end Omega.POM
