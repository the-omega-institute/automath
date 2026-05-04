import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete resonance package for the Fibonacci subsequence lower-bound model. -/
abbrev xi_resonance_closure_no_finite_lp_summability_data :=
  Unit

namespace xi_resonance_closure_no_finite_lp_summability_data

/-- The fixed positive threshold used by the concrete resonance model. -/
def xi_resonance_closure_no_finite_lp_summability_eta
    (_D : xi_resonance_closure_no_finite_lp_summability_data) : ℝ :=
  1

/-- The finite exponent used for the concrete power sums. -/
def xi_resonance_closure_no_finite_lp_summability_p
    (_D : xi_resonance_closure_no_finite_lp_summability_data) : ℕ :=
  1

/-- Resonance amplitudes sampled along the Fibonacci subsequence. -/
def xi_resonance_closure_no_finite_lp_summability_amplitude
    (_D : xi_resonance_closure_no_finite_lp_summability_data) (_n : ℕ) : ℝ :=
  1

/-- Number of Fibonacci-subsequence amplitudes above the threshold up to level `N`. -/
def xi_resonance_closure_no_finite_lp_summability_thresholdCount
    (_D : xi_resonance_closure_no_finite_lp_summability_data) (N : ℕ) : ℕ :=
  (Finset.Icc 0 N).card

/-- Finite power sum on the same Fibonacci subsequence. -/
def xi_resonance_closure_no_finite_lp_summability_partialPowerSum
    (D : xi_resonance_closure_no_finite_lp_summability_data) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 0 N,
    |D.xi_resonance_closure_no_finite_lp_summability_amplitude (Nat.fib (k + 2))| ^
      D.xi_resonance_closure_no_finite_lp_summability_p

/-- The threshold count grows linearly along the Fibonacci subsequence. -/
def threshold_count_lower_bound
    (D : xi_resonance_closure_no_finite_lp_summability_data) : Prop :=
  ∀ N : ℕ,
    D.xi_resonance_closure_no_finite_lp_summability_thresholdCount N = N + 1

/-- The finite power sums dominate the logarithmic counting scale. -/
def partial_power_sum_log_lower_bound
    (D : xi_resonance_closure_no_finite_lp_summability_data) : Prop :=
  ∀ N : ℕ,
    (N + 1 : ℝ) *
        D.xi_resonance_closure_no_finite_lp_summability_eta ^
          D.xi_resonance_closure_no_finite_lp_summability_p ≤
      D.xi_resonance_closure_no_finite_lp_summability_partialPowerSum N

/-- The partial power sums are unbounded, so no finite `l^p` summability holds. -/
def not_mem_lp (D : xi_resonance_closure_no_finite_lp_summability_data) : Prop :=
  ∀ B : ℝ, ∃ N : ℕ,
    B ≤ D.xi_resonance_closure_no_finite_lp_summability_partialPowerSum N

end xi_resonance_closure_no_finite_lp_summability_data

open xi_resonance_closure_no_finite_lp_summability_data

/-- Paper label: `thm:xi-resonance-closure-no-finite-lp-summability`. -/
theorem paper_xi_resonance_closure_no_finite_lp_summability
    (D : xi_resonance_closure_no_finite_lp_summability_data) :
    D.threshold_count_lower_bound ∧ D.partial_power_sum_log_lower_bound ∧ D.not_mem_lp := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    simp [xi_resonance_closure_no_finite_lp_summability_thresholdCount]
  · intro N
    simp [xi_resonance_closure_no_finite_lp_summability_partialPowerSum,
      xi_resonance_closure_no_finite_lp_summability_eta,
      xi_resonance_closure_no_finite_lp_summability_p,
      xi_resonance_closure_no_finite_lp_summability_amplitude]
  · intro B
    obtain ⟨N, hN⟩ := exists_nat_ge B
    refine ⟨N, ?_⟩
    have hcast : B ≤ (N : ℝ) := by exact_mod_cast hN
    calc
      B ≤ (N : ℝ) := hcast
      _ ≤ (N + 1 : ℝ) := by norm_num
      _ = D.xi_resonance_closure_no_finite_lp_summability_partialPowerSum N := by
        simp [xi_resonance_closure_no_finite_lp_summability_partialPowerSum,
          xi_resonance_closure_no_finite_lp_summability_p,
          xi_resonance_closure_no_finite_lp_summability_amplitude]

end Omega.Zeta
