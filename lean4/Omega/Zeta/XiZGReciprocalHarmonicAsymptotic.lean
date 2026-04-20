import Mathlib.Tactic
import Omega.Zeta.XiZGCountingPowerSavingError

namespace Omega.Zeta

/-- Concrete Abel-summation package for the reciprocal harmonic asymptotic attached to the
Zeckendorf--Gödel counting function. The data extend the counting package by recording the
endpoint and tail remainders after partial summation, each with the same target decay. -/
structure XiZGReciprocalHarmonicData extends XiZGCountingData where
  reciprocalSum : ℝ → ℝ
  harmonicConstant : ℝ
  endpointError : ℝ → ℝ
  tailError : ℝ → ℝ → ℝ
  errorConstant : ℝ → ℝ
  abelDecomposition :
    ∀ ε > 0, ε < 1 / 2 → ∀ X ≥ 1,
      reciprocalSum X - (deltaZG * Real.log X + harmonicConstant) =
        endpointError X + tailError ε X
  endpointBound :
    ∀ ε > 0, ε < 1 / 2 → ∀ X ≥ 1,
      |endpointError X| ≤ (errorConstant ε / 2) * Real.rpow X (-1 / 2 + ε)
  tailBound :
    ∀ ε > 0, ε < 1 / 2 → ∀ X ≥ 1,
      |tailError ε X| ≤ (errorConstant ε / 2) * Real.rpow X (-1 / 2 + ε)

/-- The reciprocal harmonic sum inherits a logarithmic main term and an
`X^(-1 / 2 + ε)` remainder once the Abel-summation endpoint and tail are each controlled at that
scale.
    cor:xi-zg-reciprocal-harmonic-asymptotic -/
theorem paper_xi_zg_reciprocal_harmonic_asymptotic (D : XiZGReciprocalHarmonicData) :
    ∀ ε > 0, ε < 1 / 2 → ∃ C_ZG : ℝ, ∀ X ≥ 1,
      |D.reciprocalSum X - (D.deltaZG * Real.log X + C_ZG)| ≤
        D.errorConstant ε * Real.rpow X (-1 / 2 + ε) := by
  intro ε hε hlt
  have _hcount := paper_xi_zg_counting_power_saving_error D.toXiZGCountingData ε hε
  refine ⟨D.harmonicConstant, ?_⟩
  intro X hX
  calc
    |D.reciprocalSum X - (D.deltaZG * Real.log X + D.harmonicConstant)| =
        |D.endpointError X + D.tailError ε X| := by
          rw [D.abelDecomposition ε hε hlt X hX]
    _ ≤ |D.endpointError X| + |D.tailError ε X| := abs_add_le _ _
    _ ≤ (D.errorConstant ε / 2) * Real.rpow X (-1 / 2 + ε) +
        (D.errorConstant ε / 2) * Real.rpow X (-1 / 2 + ε) := by
          exact add_le_add (D.endpointBound ε hε hlt X hX) (D.tailBound ε hε hlt X hX)
    _ = D.errorConstant ε * Real.rpow X (-1 / 2 + ε) := by ring

end Omega.Zeta
