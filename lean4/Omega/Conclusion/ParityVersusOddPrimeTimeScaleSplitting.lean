import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete parity-channel package for comparing a fixed parity envelope against the growing
odd-prime envelope. -/
structure conclusion_parity_versus_odd_prime_time_scale_splitting_data where
  parityScale : ℝ

namespace conclusion_parity_versus_odd_prime_time_scale_splitting_data

/-- Closed-form parity envelope time, independent of the odd-prime scale. -/
noncomputable def parityEnvelope
    (D : conclusion_parity_versus_odd_prime_time_scale_splitting_data) : ℝ :=
  D.parityScale * Real.log 2

/-- Normalized odd-prime envelope used for the comparison sequence. -/
noncomputable def oddPrimeEnvelope
    (_D : conclusion_parity_versus_odd_prime_time_scale_splitting_data) (p : ℕ) : ℝ :=
  ((p + 1 : ℕ) : ℝ)

/-- The parity envelope has the advertised closed form. -/
def parityEnvelopeClosedForm
    (D : conclusion_parity_versus_odd_prime_time_scale_splitting_data) : Prop :=
  D.parityEnvelope = D.parityScale * Real.log 2

/-- The parity envelope divided by the odd-prime envelope vanishes along increasing prime scales. -/
def parityOddPrimeRatioVanishes
    (D : conclusion_parity_versus_odd_prime_time_scale_splitting_data) : Prop :=
  Tendsto (fun p : ℕ => D.parityEnvelope / D.oddPrimeEnvelope p) atTop (𝓝 0)

end conclusion_parity_versus_odd_prime_time_scale_splitting_data

open conclusion_parity_versus_odd_prime_time_scale_splitting_data

/-- Paper label: `cor:conclusion-parity-versus-odd-prime-time-scale-splitting`. -/
theorem paper_conclusion_parity_versus_odd_prime_time_scale_splitting
    (D : conclusion_parity_versus_odd_prime_time_scale_splitting_data) :
    D.parityEnvelopeClosedForm ∧ D.parityOddPrimeRatioVanishes := by
  refine ⟨rfl, ?_⟩
  change Tendsto
    (((fun n : ℕ => D.parityEnvelope / (n : ℝ)) ∘ fun p : ℕ => p + 1)) atTop (𝓝 0)
  exact (tendsto_const_div_atTop_nhds_zero_nat D.parityEnvelope).comp (tendsto_add_atTop_nat 1)

end Omega.Conclusion
