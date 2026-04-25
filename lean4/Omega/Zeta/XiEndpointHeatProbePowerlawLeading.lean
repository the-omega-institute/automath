import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointAtomSeparation

open Filter
open scoped Topology

namespace Omega.Zeta

/-- The explicit leading coefficient in the concrete integer-order endpoint power-law model. -/
noncomputable def xi_endpoint_heat_probe_powerlaw_leading_coefficient
    (KPlus KMinus : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k + 1) * (Nat.factorial k : ℝ) * (KPlus + KMinus)

/-- Concrete endpoint heat-probe sequence with endpoint atom `m_{-1}` and a power-law remainder
of order `k + 1`. -/
noncomputable def xi_endpoint_heat_probe_powerlaw_leading_sequence
    (mMinusOne KPlus KMinus : ℝ) (k N : ℕ) : ℝ :=
  xiEndpointAtomMass mMinusOne +
    xiEndpointHeatProbeRegularVariationTerm
      (xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k) k N

/-- Paper label: `thm:xi-endpoint-heat-probe-powerlaw-leading`. In the concrete integer-order
endpoint model, separating the atom at `-1` leaves an explicit regularly varying tail whose
normalized leading coefficient is `2^(2k+1) k! (K_+ + K_-)`. -/
theorem paper_xi_endpoint_heat_probe_powerlaw_leading
    (mMinusOne KPlus KMinus : ℝ) (k : ℕ) (hKPlus : 0 ≤ KPlus) (hKMinus : 0 ≤ KMinus) :
    (∀ N : ℕ,
      xi_endpoint_heat_probe_powerlaw_leading_sequence mMinusOne KPlus KMinus k N -
          xiEndpointAtomMass mMinusOne =
        xiEndpointHeatProbeRegularVariationTerm
          (xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k) k N) ∧
      Tendsto
        (fun N : ℕ =>
          ((N + 1 : ℝ) ^ (k + 1)) *
            (xi_endpoint_heat_probe_powerlaw_leading_sequence mMinusOne KPlus KMinus k N -
              xiEndpointAtomMass mMinusOne))
        atTop (𝓝 (xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k)) ∧
      (0 < xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k ↔
        0 < KPlus + KMinus) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    simp [xi_endpoint_heat_probe_powerlaw_leading_sequence, xiEndpointAtomMass]
  · have htail :
        Tendsto
          (fun N : ℕ =>
            ((N + 1 : ℝ) ^ (k + 1)) *
              xiEndpointHeatProbeRegularVariationTerm
                (xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k) k N)
          atTop (𝓝 (xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k)) :=
      (paper_xi_endpoint_heat_probe_rstar_regular_variation_tail 1 mMinusOne
        (xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k) k
        (by positivity)).2
    simpa [xi_endpoint_heat_probe_powerlaw_leading_sequence, xiEndpointAtomMass] using htail
  · constructor
    · intro hcoeff
      have hsum_nonneg : 0 ≤ KPlus + KMinus := add_nonneg hKPlus hKMinus
      by_cases hsum_zero : KPlus + KMinus = 0
      · have hcoeff_zero :
            xi_endpoint_heat_probe_powerlaw_leading_coefficient KPlus KMinus k = 0 := by
          simp [xi_endpoint_heat_probe_powerlaw_leading_coefficient, hsum_zero]
        linarith
      · exact lt_of_le_of_ne hsum_nonneg (Ne.symm hsum_zero)
    · intro hsum
      unfold xi_endpoint_heat_probe_powerlaw_leading_coefficient
      refine mul_pos ?_ hsum
      refine mul_pos ?_ ?_
      · positivity
      · exact_mod_cast Nat.factorial_pos k

end Omega.Zeta
