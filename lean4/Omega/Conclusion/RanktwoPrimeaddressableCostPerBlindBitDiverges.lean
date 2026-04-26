import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence
import Omega.Conclusion.RanktwoPrimeaddressableExactPrimorialOptimum

namespace Omega.Conclusion

open Filter

noncomputable section

/-- Concrete asymptotic certificate for rank-two prime-addressable primorial cost per blind bit. -/
structure conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data where
  Lpa : ℕ → ℝ
  primorialLog : ℕ → ℝ
  thetaAtPrime : ℕ → ℝ
  blindBits : ℕ → ℝ
  c : ℝ
  R : ℕ
  R_pos : 1 ≤ R
  c_pos : 0 < c
  exact_lower : ∀ r : ℕ, primorialLog r ≤ Lpa r
  exact_upper : ∀ r : ℕ, Lpa r ≤ primorialLog r
  primorial_eq_theta : ∀ r : ℕ, primorialLog r = thetaAtPrime r
  theta_lower : ∀ r : ℕ, R ≤ r → c * (r : ℝ) * Real.log (r : ℝ) ≤ thetaAtPrime r
  blindBits_eq : ∀ r : ℕ, R ≤ r → blindBits r = (r : ℝ)

namespace conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data

/-- The per-blind-bit logarithmic cost. -/
def cost_per_blind_bit
    (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) (r : ℕ) : ℝ :=
  C.Lpa r / C.blindBits r

/-- The theorem statement: exact optimum, logarithmic lower bound per bit, and divergence. -/
def statement (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) : Prop :=
  (∀ r : ℕ, C.Lpa r = C.primorialLog r) ∧
    (∀ r : ℕ, C.R ≤ r → C.c * Real.log (r : ℝ) ≤ C.cost_per_blind_bit r) ∧
      NatDivergesToInfinity C.cost_per_blind_bit

lemma exact_optimum
    (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) :
    ∀ r : ℕ, C.Lpa r = C.primorialLog r :=
  paper_conclusion_ranktwo_primeaddressable_exact_primorial_optimum
    C.Lpa C.primorialLog C.exact_lower C.exact_upper

lemma per_bit_log_lower
    (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) :
    ∀ r : ℕ, C.R ≤ r → C.c * Real.log (r : ℝ) ≤ C.cost_per_blind_bit r := by
  intro r hr
  have hopt : C.Lpa r = C.primorialLog r := C.exact_optimum r
  have hr_pos_nat : 0 < r := lt_of_lt_of_le C.R_pos hr
  have hr_pos : 0 < (r : ℝ) := Nat.cast_pos.mpr hr_pos_nat
  have hcost : C.cost_per_blind_bit r = C.thetaAtPrime r / (r : ℝ) := by
    simp [cost_per_blind_bit, hopt, C.primorial_eq_theta r, C.blindBits_eq r hr]
  rw [hcost]
  exact (le_div_iff₀ hr_pos).2 (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using C.theta_lower r hr)

lemma log_term_large_after_R
    (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) :
    ∀ K : ℕ, ∃ r : ℕ, C.R ≤ r ∧ (K : ℝ) ≤ C.c * Real.log (r : ℝ) := by
  have hlog : Tendsto (fun r : ℕ => C.c * Real.log (r : ℝ)) atTop atTop := by
    exact Tendsto.const_mul_atTop C.c_pos
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  intro K
  have hEventually : ∀ᶠ r : ℕ in atTop, (K : ℝ) ≤ C.c * Real.log (r : ℝ) :=
    hlog.eventually_ge_atTop (K : ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hEventually
  refine ⟨max C.R N, le_max_left C.R N, ?_⟩
  exact hN (max C.R N) (le_max_right C.R N)

lemma log_term_diverges
    (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) :
    NatDivergesToInfinity (fun r : ℕ => C.c * Real.log (r : ℝ)) := by
  intro K
  obtain ⟨r, _hrR, hrlog⟩ := C.log_term_large_after_R K
  exact ⟨r, hrlog⟩

lemma cost_per_blind_bit_diverges
    (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) :
    NatDivergesToInfinity C.cost_per_blind_bit := by
  intro K
  obtain ⟨r, hrR, hrlog⟩ := C.log_term_large_after_R K
  exact ⟨r, le_trans hrlog (C.per_bit_log_lower r hrR)⟩

end conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data

/-- Paper label: `cor:conclusion-ranktwo-primeaddressable-cost-per-blind-bit-diverges`.
The exact primorial optimum and a Chebyshev-type lower certificate for `θ(p_r)` imply that the
logarithmic cost per blind bit dominates a positive multiple of `log r`, hence diverges. -/
theorem paper_conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges
    (C : conclusion_ranktwo_primeaddressable_cost_per_blind_bit_diverges_data) : C.statement := by
  exact ⟨C.exact_optimum, C.per_bit_log_lower, C.cost_per_blind_bit_diverges⟩

end

end Omega.Conclusion
