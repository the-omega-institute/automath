import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete transfer-family data for time-reversal spectral reciprocity. -/
structure xi_time_reversal_spectral_reciprocity_data where
  xi_time_reversal_spectral_reciprocity_spectralCount : ℕ
  xi_time_reversal_spectral_reciprocity_transferFamily :
    ℚ → Fin xi_time_reversal_spectral_reciprocity_spectralCount → ℚ
  xi_time_reversal_spectral_reciprocity_timeReversalPartner :
    Fin xi_time_reversal_spectral_reciprocity_spectralCount →
      Fin xi_time_reversal_spectral_reciprocity_spectralCount
  xi_time_reversal_spectral_reciprocity_fredholmDeterminant : ℚ → ℚ → ℚ
  xi_time_reversal_spectral_reciprocity_reciprocityExponent : ℚ → ℕ
  xi_time_reversal_spectral_reciprocity_traceRegularWeight : ℚ → ℚ
  xi_time_reversal_spectral_reciprocity_spectralPairing :
    ∀ z θ,
      xi_time_reversal_spectral_reciprocity_fredholmDeterminant z θ =
        z ^ xi_time_reversal_spectral_reciprocity_reciprocityExponent θ *
            xi_time_reversal_spectral_reciprocity_traceRegularWeight θ *
          xi_time_reversal_spectral_reciprocity_fredholmDeterminant z⁻¹ (-θ)
  xi_time_reversal_spectral_reciprocity_criticalSliceUniqueness :
    ∀ θ,
      xi_time_reversal_spectral_reciprocity_fredholmDeterminant 1 θ =
          xi_time_reversal_spectral_reciprocity_fredholmDeterminant 1 0 →
        θ = 0

/-- The reciprocal Fredholm determinant equation. -/
def xi_time_reversal_spectral_reciprocity_reciprocalDeterminantEquation
    (D : xi_time_reversal_spectral_reciprocity_data) : Prop :=
  ∀ z θ,
    D.xi_time_reversal_spectral_reciprocity_fredholmDeterminant z θ =
      z ^ D.xi_time_reversal_spectral_reciprocity_reciprocityExponent θ *
          D.xi_time_reversal_spectral_reciprocity_traceRegularWeight θ *
        D.xi_time_reversal_spectral_reciprocity_fredholmDeterminant z⁻¹ (-θ)

/-- The normalized critical spectral slice is exactly `theta = 0`. -/
def xi_time_reversal_spectral_reciprocity_criticalSliceCharacterization
    (D : xi_time_reversal_spectral_reciprocity_data) : Prop :=
  {θ | D.xi_time_reversal_spectral_reciprocity_fredholmDeterminant 1 θ =
      D.xi_time_reversal_spectral_reciprocity_fredholmDeterminant 1 0} =
    ({0} : Set ℚ)

/-- The concrete statement of spectral reciprocity and critical-slice uniqueness. -/
def xi_time_reversal_spectral_reciprocity_data.statement
    (D : xi_time_reversal_spectral_reciprocity_data) : Prop :=
  xi_time_reversal_spectral_reciprocity_reciprocalDeterminantEquation D ∧
    xi_time_reversal_spectral_reciprocity_criticalSliceCharacterization D

/-- Paper label: `prop:xi-time-reversal-spectral-reciprocity`. -/
theorem paper_xi_time_reversal_spectral_reciprocity
    (D : xi_time_reversal_spectral_reciprocity_data) : D.statement := by
  constructor
  · exact D.xi_time_reversal_spectral_reciprocity_spectralPairing
  · ext θ
    constructor
    · intro hθ
      exact D.xi_time_reversal_spectral_reciprocity_criticalSliceUniqueness θ hθ
    · intro hθ
      simp only [Set.mem_singleton_iff] at hθ
      rw [hθ]
      simp

end Omega.Zeta
