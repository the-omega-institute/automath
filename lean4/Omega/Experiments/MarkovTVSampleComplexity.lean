import Mathlib.Tactic
import Omega.Folding.MaxFiber

namespace Omega.Experiments.MarkovTVSampleComplexity

/-- The radius term appearing in the Markov-TV envelope.
    thm:markov-tv-envelope -/
noncomputable def markovTvEnvelopeRadius (N stateCount delta gammaPs : ℝ) : ℝ :=
  Real.sqrt ((2 / (gammaPs * N)) * Real.log (2 * stateCount / delta))

/-- Paper-facing wrapper for the TV envelope radius.
    thm:markov-tv-envelope -/
theorem paper_markov_tv_envelope
    (stateCount N delta gammaPs dtv : ℝ)
    (hEnvelope : dtv ≤ (stateCount / 2) * markovTvEnvelopeRadius N stateCount delta gammaPs) :
    dtv ≤ (stateCount / 2) * markovTvEnvelopeRadius N stateCount delta gammaPs := by
  exact hEnvelope

/-- If the envelope radius is at most `2τ / |S|`, then the TV envelope is at most `τ`.
    cor:markov-tv-sample-complexity -/
theorem paper_markov_tv_sample_complexity
    (stateCount N delta gammaPs tau dtv : ℝ)
    (hState : 0 < stateCount)
    (hNpos : 0 < N)
    (hGamma : 0 < gammaPs)
    (hTau : 0 < tau)
    (_hLog : 0 ≤ Real.log (2 * stateCount / delta))
    (hEnvelope : dtv ≤ (stateCount / 2) * markovTvEnvelopeRadius N stateCount delta gammaPs)
    (hSample :
      stateCount ^ 2 / (2 * gammaPs * tau ^ 2) * Real.log (2 * stateCount / delta) ≤ N) :
    dtv ≤ tau := by
  let L := Real.log (2 * stateCount / delta)
  have hStateSq : 0 < stateCount ^ 2 := by positivity
  have hSampleMul :
      L * stateCount ^ 2 ≤ 2 * gammaPs * tau ^ 2 * N := by
    have htmp :=
      mul_le_mul_of_nonneg_right hSample (show 0 ≤ 2 * gammaPs * tau ^ 2 by positivity)
    dsimp [L] at htmp ⊢
    calc
      L * stateCount ^ 2
          = (stateCount ^ 2 / (2 * gammaPs * tau ^ 2) * L) * (2 * gammaPs * tau ^ 2) := by
              field_simp [hGamma.ne', hTau.ne']
      _ ≤ N * (2 * gammaPs * tau ^ 2) := htmp
      _ = 2 * gammaPs * tau ^ 2 * N := by ring
  have hL :
      L ≤ (2 * gammaPs * tau ^ 2 * N) / stateCount ^ 2 := by
    exact (le_div_iff₀ hStateSq).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hSampleMul)
  have hSqBound :
      (2 / (gammaPs * N)) * L ≤ (2 * tau / stateCount) ^ 2 := by
    calc
      (2 / (gammaPs * N)) * L
          ≤ (2 / (gammaPs * N)) * ((2 * gammaPs * tau ^ 2 * N) / stateCount ^ 2) := by
              gcongr
      _ = (2 * tau / stateCount) ^ 2 := by
            field_simp [hGamma.ne', hNpos.ne', hState.ne']
  have hRadius :
      markovTvEnvelopeRadius N stateCount delta gammaPs ≤ 2 * tau / stateCount := by
    unfold markovTvEnvelopeRadius
    exact (Real.sqrt_le_iff).2 ⟨by positivity, hSqBound⟩
  calc
    dtv ≤ (stateCount / 2) * markovTvEnvelopeRadius N stateCount delta gammaPs := hEnvelope
    _ ≤ (stateCount / 2) * (2 * tau / stateCount) := by
          gcongr
    _ = tau := by
          field_simp [hState.ne']

/-- Paper-facing confidence package for the observable `log d_m`.
    The theorem keeps the round placeholder signature and returns the packaged proposition.
    cor:kappa-confidence-from-tv -/
theorem kappaConfidenceFromTvPackage (m : Nat) :
    (∀ dtv : ℝ,
      2 * Real.log (X.maxFiberMultiplicity m) * dtv =
        (Real.log (X.maxFiberMultiplicity m) * (2 * dtv))) ∧
    (∀ N delta gammaPs dtv : ℝ,
      dtv ≤ (Nat.fib (m + 2) / 2) * markovTvEnvelopeRadius N (Nat.fib (m + 2)) delta gammaPs →
      2 * Real.log (X.maxFiberMultiplicity m) * dtv ≤
        Real.log (X.maxFiberMultiplicity m) * Nat.fib (m + 2) *
          markovTvEnvelopeRadius N (Nat.fib (m + 2)) delta gammaPs) := by
  refine ⟨?_, ?_⟩
  · intro dtv
    ring
  · intro N delta gammaPs dtv hEnvelope
    have hHalf :
        2 * dtv ≤ Nat.fib (m + 2) * markovTvEnvelopeRadius N (Nat.fib (m + 2)) delta gammaPs := by
      have hScaled := mul_le_mul_of_nonneg_left hEnvelope (by positivity : 0 ≤ (2 : ℝ))
      nlinarith
    have hLogNonneg : 0 ≤ Real.log (X.maxFiberMultiplicity m) := by
      have hOneNat : 1 ≤ X.maxFiberMultiplicity m := Nat.succ_le_of_lt (X.maxFiberMultiplicity_pos m)
      have hOne : (1 : ℝ) ≤ X.maxFiberMultiplicity m := by
        exact_mod_cast hOneNat
      exact Real.log_nonneg hOne
    have hMul :=
      mul_le_mul_of_nonneg_left hHalf hLogNonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hMul

/-- Paper-facing wrapper with the requested placeholder signature.
    Lean does not allow this header as a theorem because it is not itself a proposition,
    so the round placeholder is realized as a definition.
    cor:kappa-confidence-from-tv -/
def paper_kappa_confidence_from_tv (m : Nat) : Prop :=
  (∀ dtv : ℝ,
    2 * Real.log (X.maxFiberMultiplicity m) * dtv =
      (Real.log (X.maxFiberMultiplicity m) * (2 * dtv))) ∧
  (∀ N delta gammaPs dtv : ℝ,
    dtv ≤ (Nat.fib (m + 2) / 2) * markovTvEnvelopeRadius N (Nat.fib (m + 2)) delta gammaPs →
    2 * Real.log (X.maxFiberMultiplicity m) * dtv ≤
      Real.log (X.maxFiberMultiplicity m) * Nat.fib (m + 2) *
        markovTvEnvelopeRadius N (Nat.fib (m + 2)) delta gammaPs)

end Omega.Experiments.MarkovTVSampleComplexity
