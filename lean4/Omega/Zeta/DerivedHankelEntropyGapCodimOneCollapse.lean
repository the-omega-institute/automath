import Mathlib.Tactic
import Omega.Zeta.XiEntropyGapExponentialSuppressionNonzeroFingerprint
import Omega.Zeta.XiHankelSpikeSingularSpectrumSeparation

namespace Omega.Zeta

/-- Rewriting the singular-spectrum separation theorem in the entropy-gap normalization
`u₀ = 4π S_def` and `B = 4π e⁻¹ ε` gives the codimension-one collapse statement. 
    thm:derived-hankel-entropy-gap-codim-one-collapse -/
theorem paper_derived_hankel_entropy_gap_codim_one_collapse
    (D : Omega.Zeta.XiHankelSpikeSingularSpectrumData) (Sdef eps : ℝ)
    (hu0 : D.u0 = 4 * Real.pi * Sdef) (hB : D.B = 4 * Real.pi * Real.exp (-1) * eps) :
    (4 * Real.pi * Sdef - 4 * Real.pi * (D.κ : ℝ) * Real.exp (-1) * eps ≤ D.singularValue 1) ∧
      (∀ j : ℕ, 2 ≤ j → D.singularValue j ≤ 4 * Real.pi * (D.κ : ℝ) * Real.exp (-1) * eps) := by
  rcases paper_xi_hankel_spike_singular_spectrum_separation D with ⟨hlead, htail⟩
  refine ⟨?_, ?_⟩
  · have hlead' : |4 * Real.pi * Sdef| - (D.κ : ℝ) * D.B ≤ D.singularValue 1 := by
      simpa [hu0] using hlead
    have habs : 4 * Real.pi * Sdef ≤ |4 * Real.pi * Sdef| := le_abs_self _
    have hgoal' : 4 * Real.pi * Sdef - (D.κ : ℝ) * D.B ≤ D.singularValue 1 := by
      linarith
    simpa [hB, mul_assoc, mul_left_comm, mul_comm] using hgoal'
  · intro j hj
    have htail' : D.singularValue j ≤ (D.κ : ℝ) * D.B := htail j hj
    simpa [hB, mul_assoc, mul_left_comm, mul_comm] using htail'

end Omega.Zeta
