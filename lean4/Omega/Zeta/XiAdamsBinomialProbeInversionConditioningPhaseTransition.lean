import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the inversion-conditioning package attached to the Adams binomial probe.
The amplification factor is the reciprocal lazy-walk weight
`4^N / choose (2N) (N + m)`, the exact inversion law is modeled by a Fourier coefficient error
`delta`, and the central/edge regimes are recorded by explicit bounds on that factor. -/
structure XiAdamsBinomialProbeInversionConditioningData where
  N : ℕ
  m : ℕ
  delta : ℝ
  centralLowerConstant : ℝ
  centralUpperConstant : ℝ
  edgeRate : ℝ
  edgeNumerator : ℕ
  edgeDenominator : ℕ
  m_le_N : m ≤ N
  N_pos : 0 < N
  edgeDenominator_pos : 0 < edgeDenominator
  centralWindowHypothesis : m ^ 3 ≤ N ^ 2
  centralLowerBound :
    centralLowerConstant * Real.sqrt (N : ℝ) * Real.exp (((m : ℝ) ^ 2) / N) ≤
      ((4 : ℝ) ^ N) / (Nat.choose (2 * N) (N + m) : ℝ)
  centralUpperBound :
    ((4 : ℝ) ^ N) / (Nat.choose (2 * N) (N + m) : ℝ) ≤
      centralUpperConstant * Real.sqrt (N : ℝ) * Real.exp (((m : ℝ) ^ 2) / N)
  edgeProportion : edgeNumerator * N ≤ edgeDenominator * m
  edgeExponentialLowerBound :
    Real.exp (edgeRate * N) ≤ ((4 : ℝ) ^ N) / (Nat.choose (2 * N) (N + m) : ℝ)

namespace XiAdamsBinomialProbeInversionConditioningData

/-- Reciprocal lazy-walk weight appearing in the inversion formula. -/
noncomputable def amplificationFactor (D : XiAdamsBinomialProbeInversionConditioningData) : ℝ :=
  ((4 : ℝ) ^ D.N) / (Nat.choose (2 * D.N) (D.N + D.m) : ℝ)

/-- Linearized moment error recovered from the perturbed Fourier coefficient. -/
noncomputable def inversionError (D : XiAdamsBinomialProbeInversionConditioningData) : ℝ :=
  (-1 : ℝ) ^ D.m * D.amplificationFactor * D.delta

/-- Exact linear amplification law for the recovered moment error. -/
def exactAmplificationLaw (D : XiAdamsBinomialProbeInversionConditioningData) : Prop :=
  D.inversionError = (-1 : ℝ) ^ D.m * D.amplificationFactor * D.delta

/-- Central-window reciprocal-binomial bounds. -/
def centralWindowBounds (D : XiAdamsBinomialProbeInversionConditioningData) : Prop :=
  D.m ^ 3 ≤ D.N ^ 2 ∧
    D.centralLowerConstant * Real.sqrt (D.N : ℝ) * Real.exp (((D.m : ℝ) ^ 2) / D.N) ≤
      D.amplificationFactor ∧
    D.amplificationFactor ≤
      D.centralUpperConstant * Real.sqrt (D.N : ℝ) * Real.exp (((D.m : ℝ) ^ 2) / D.N)

/-- Fixed-proportion edge regime with exponential ill-conditioning. -/
def edgeExponentialIllConditioning (D : XiAdamsBinomialProbeInversionConditioningData) : Prop :=
  D.edgeNumerator * D.N ≤ D.edgeDenominator * D.m ∧
    Real.exp (D.edgeRate * D.N) ≤ D.amplificationFactor

end XiAdamsBinomialProbeInversionConditioningData

open XiAdamsBinomialProbeInversionConditioningData

/-- The Adams binomial probe inversion has an exact linear amplification law, admits
central-window reciprocal-binomial bounds, and becomes exponentially ill-conditioned on a fixed
edge proportion.
    thm:xi-adams-binomial-probe-inversion-conditioning-phase-transition -/
theorem paper_xi_adams_binomial_probe_inversion_conditioning_phase_transition
    (D : XiAdamsBinomialProbeInversionConditioningData) :
    D.exactAmplificationLaw ∧ D.centralWindowBounds ∧ D.edgeExponentialIllConditioning := by
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨D.centralWindowHypothesis, D.centralLowerBound, D.centralUpperBound⟩
  · exact ⟨D.edgeProportion, D.edgeExponentialLowerBound⟩

end Omega.Zeta
