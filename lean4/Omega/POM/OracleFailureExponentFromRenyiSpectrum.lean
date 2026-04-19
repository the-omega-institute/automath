import Mathlib.Tactic
import Omega.POM.MaxFiberPublication

namespace Omega.POM

/-- The finite-volume Rényi spectrum used to control the oracle failure exponent. -/
noncomputable def oracleRenyiSpectrum (q m : ℕ) : ℝ :=
  Omega.momentSum q m

/-- The max-fiber lower envelope extracted from the collision moment bound. -/
noncomputable def oracleFailureLowerEnvelope (q m : ℕ) : ℝ :=
  ((Omega.X.maxFiberMultiplicity m : ℕ) ^ q : ℝ)

/-- Pointwise lower bound for the oracle failure exponent along the Rényi-spectrum family. -/
def oracleFailureExponentLowerBound (q : ℕ) : Prop :=
  ∀ m : ℕ, oracleFailureLowerEnvelope q m ≤ oracleRenyiSpectrum q m

/-- Eventual form of the same lower bound, viewed as a liminf-style exponent inequality. -/
def oracleFailureExponentLiminfLowerBound (q : ℕ) : Prop :=
  ∃ N : ℕ, ∀ m ≥ N, oracleFailureLowerEnvelope q m ≤ oracleRenyiSpectrum q m

/-- The max-fiber moment inequality gives a concrete finite-volume lower envelope for the
oracle failure exponent, and therefore the same lower envelope survives in the eventual/liminf
package.
    cor:oracle-failure-exponent-from-renyi-spectrum -/
theorem paper_oracle_failure_exponent_from_renyi_spectrum (q : ℕ) :
    oracleFailureExponentLowerBound q ∧ oracleFailureExponentLiminfLowerBound q := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa [oracleFailureLowerEnvelope, oracleRenyiSpectrum] using
      (show (((Omega.X.maxFiberMultiplicity m : ℕ) ^ q : ℕ) : ℝ) ≤
          (Omega.momentSum q m : ℝ) by
        exact_mod_cast (paper_projection_max_fiber q m).1)
  · refine ⟨0, ?_⟩
    intro m _hm
    simpa [oracleFailureLowerEnvelope, oracleRenyiSpectrum] using
      (show (((Omega.X.maxFiberMultiplicity m : ℕ) ^ q : ℕ) : ℝ) ≤
          (Omega.momentSum q m : ℝ) by
        exact_mod_cast (paper_projection_max_fiber q m).1)

end Omega.POM
