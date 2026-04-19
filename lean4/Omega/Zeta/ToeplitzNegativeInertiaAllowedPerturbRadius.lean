import Mathlib.Tactic
import Omega.Zeta.ToeplitzNegativeInertiaSpectralGapStability

namespace Omega.Zeta

/-- Concrete perturbative data for the Toeplitz negative-inertia radius corollary. The
conjugated perturbation norm is bounded by `‖R‖² ‖E_N‖`, and any perturbation below the spectral
gap `g_N` preserves the negative inertia count. -/
structure ToeplitzNegativeInertiaAllowedPerturbRadiusData where
  opNormEN : ℝ
  gN : ℝ
  opNormR : ℝ
  conjugatedPerturbationNorm : ℝ
  negativeInertiaPreserved : Prop
  gN_pos : 0 < gN
  conjugatedPerturbationBound :
    conjugatedPerturbationNorm ≤ opNormR ^ 2 * opNormEN
  negativeInertia_of_conjugatedSmall :
    conjugatedPerturbationNorm < gN → negativeInertiaPreserved

/-- Paper-facing corollary: the perturbation radius `g_N / ‖R‖²` guarantees preservation of the
negative inertia count after conjugation.
    cor:xi-toeplitz-negative-inertia-allowed-perturb-radius -/
theorem paper_xi_toeplitz_negative_inertia_allowed_perturb_radius
    (D : ToeplitzNegativeInertiaAllowedPerturbRadiusData) :
    D.opNormEN < D.gN / D.opNormR ^ 2 → D.negativeInertiaPreserved := by
  intro hRadius
  have hConjugatedSmall : D.conjugatedPerturbationNorm < D.gN := by
    by_cases hR : D.opNormR = 0
    · have hBoundZero : D.conjugatedPerturbationNorm ≤ 0 := by
        simpa [hR] using D.conjugatedPerturbationBound
      exact lt_of_le_of_lt hBoundZero D.gN_pos
    · have hR2pos : 0 < D.opNormR ^ 2 := sq_pos_of_ne_zero hR
      have hScaled : D.opNormR ^ 2 * D.opNormEN < D.gN := by
        have hScaled' : D.opNormEN * D.opNormR ^ 2 < D.gN :=
          (_root_.lt_div_iff₀ hR2pos).mp hRadius
        simpa [mul_comm, mul_left_comm, mul_assoc] using hScaled'
      exact lt_of_le_of_lt D.conjugatedPerturbationBound hScaled
  let S : ToeplitzNegativeInertiaSpectralGapStabilityData :=
    { congruenceDecomposition := D.conjugatedPerturbationNorm < D.gN
      negativeInertiaPreserved := D.negativeInertiaPreserved
      explicitSpectralGapLowerBound := D.conjugatedPerturbationNorm < D.gN
      hasCongruenceDecomposition := hConjugatedSmall
      deriveNegativeInertiaPreserved := D.negativeInertia_of_conjugatedSmall
      deriveExplicitSpectralGapLowerBound := fun hSmall => hSmall }
  exact (paper_xi_toeplitz_negative_inertia_spectral_gap_stability S).1

end Omega.Zeta
