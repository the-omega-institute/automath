import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter Topology
open scoped BigOperators

/-- Concrete binary symmetric channel mismatch data.

The concepts are represented by integer-valued sign streams, while mismatch locations and rates
are defined directly from equality of the two streams. -/
structure xi_bsc_mismatch_information_rate_data where
  source : ℕ → ℤ
  target : ℕ → ℤ
  noise : ℕ → ℤ
  beta : ℝ
  noiseMean : ℝ
  mismatchDensity : ℝ

namespace xi_bsc_mismatch_information_rate_data

/-- Mismatch positions in the first `N` coordinates. -/
def mismatchSet (D : xi_bsc_mismatch_information_rate_data) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k => D.source k ≠ D.target k

/-- Number of mismatches in the first `N` coordinates. -/
def mismatchCount (D : xi_bsc_mismatch_information_rate_data) (N : ℕ) : ℕ :=
  (D.mismatchSet N).card

/-- Empirical mismatch density in the first `N` coordinates. -/
noncomputable def mismatchDensityPrefix (D : xi_bsc_mismatch_information_rate_data)
    (N : ℕ) : ℝ :=
  (D.mismatchCount N : ℝ) / (N : ℝ)

/-- The finite-prefix log-likelihood ratio after cancellation of matched coordinates. -/
def logLikelihoodRatioPrefix (D : xi_bsc_mismatch_information_rate_data) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun k =>
    if D.source k = D.target k then 0 else D.beta * (D.noise k : ℝ)

/-- The same finite-prefix contribution written only over mismatch locations. -/
def mismatchNoiseContributionPrefix (D : xi_bsc_mismatch_information_rate_data)
    (N : ℕ) : ℝ :=
  Finset.sum (D.mismatchSet N) fun k => D.beta * (D.noise k : ℝ)

/-- Matched coordinates cancel, so only mismatch locations contribute. -/
def logLikelihoodRatioIdentity (D : xi_bsc_mismatch_information_rate_data) : Prop :=
  ∀ N : ℕ, D.logLikelihoodRatioPrefix N = D.mismatchNoiseContributionPrefix N

/-- The strong-law hypothesis for the mismatch density. -/
def mismatchDensityExists (D : xi_bsc_mismatch_information_rate_data) : Prop :=
  Tendsto D.mismatchDensityPrefix atTop (nhds D.mismatchDensity)

/-- Prefix information rate obtained by multiplying mismatch density by the noise mean. -/
noncomputable def informationRatePrefix (D : xi_bsc_mismatch_information_rate_data)
    (N : ℕ) : ℝ :=
  D.beta * (D.noiseMean * D.mismatchDensityPrefix N)

/-- Limiting information rate. -/
def informationRateLimit (D : xi_bsc_mismatch_information_rate_data) : Prop :=
  Tendsto D.informationRatePrefix atTop (nhds (D.beta * (D.noiseMean * D.mismatchDensity)))

end xi_bsc_mismatch_information_rate_data

/-- Paper label: `prop:xi-bsc-mismatch-information-rate`. -/
theorem paper_xi_bsc_mismatch_information_rate
    (D : xi_bsc_mismatch_information_rate_data) :
    D.logLikelihoodRatioIdentity ∧ (D.mismatchDensityExists → D.informationRateLimit) := by
  constructor
  · intro N
    rw [xi_bsc_mismatch_information_rate_data.logLikelihoodRatioPrefix,
      xi_bsc_mismatch_information_rate_data.mismatchNoiseContributionPrefix,
      xi_bsc_mismatch_information_rate_data.mismatchSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases h : D.source k = D.target k
    · simp [h]
    · simp [h]
  · intro hDensity
    simpa [xi_bsc_mismatch_information_rate_data.informationRatePrefix, mul_assoc] using
      hDensity.const_mul (D.beta * D.noiseMean)

end Omega.Zeta
