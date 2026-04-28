import Mathlib.Tactic
import Omega.Conclusion.EscortTwoStateClosure

namespace Omega.Zeta

noncomputable section

/-- The closed-form residual moment of the two-state escort limit. -/
def xi_time_part9o_escort_residual_moment_identifiability_moment (q r : ℕ) : ℝ :=
  1 - (1 - (1 / Real.goldenRatio) ^ r) *
    Omega.Conclusion.conclusion_escort_two_state_closure_theta q

/-- Paper label: `thm:xi-time-part9o-escort-residual-moment-identifiability`. -/
theorem paper_xi_time_part9o_escort_residual_moment_identifiability (r : ℕ) (hr : 1 ≤ r) :
    (∀ q : ℕ,
      xi_time_part9o_escort_residual_moment_identifiability_moment q r =
        1 - (1 - (1 / Real.goldenRatio) ^ r) *
          Omega.Conclusion.conclusion_escort_two_state_closure_theta q) ∧
      Function.Injective
        (fun q : ℕ => xi_time_part9o_escort_residual_moment_identifiability_moment q r) := by
  constructor
  · intro q
    rfl
  · let a : ℝ := 1 - (1 / Real.goldenRatio) ^ r
    have hbase_nonneg : 0 ≤ (1 / Real.goldenRatio : ℝ) := by positivity
    have hbase_lt : (1 / Real.goldenRatio : ℝ) < 1 := by
      rw [one_div]
      exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    have hr_ne : r ≠ 0 := by omega
    have hpow_lt : (1 / Real.goldenRatio : ℝ) ^ r < 1 :=
      pow_lt_one₀ hbase_nonneg hbase_lt hr_ne
    have ha_pos : 0 < a := by
      dsimp [a]
      linarith
    have htheta_anti :
        StrictAnti Omega.Conclusion.conclusion_escort_two_state_closure_theta := by
      simpa [Omega.Conclusion.conclusion_escort_two_state_closure_theta] using
        (Omega.Conclusion.binfoldEscortTheta_strictAnti Real.one_lt_goldenRatio)
    intro q₁ q₂ hmoment
    have htheta :
        Omega.Conclusion.conclusion_escort_two_state_closure_theta q₁ =
          Omega.Conclusion.conclusion_escort_two_state_closure_theta q₂ := by
      have hmoment' :
          1 - a * Omega.Conclusion.conclusion_escort_two_state_closure_theta q₁ =
            1 - a * Omega.Conclusion.conclusion_escort_two_state_closure_theta q₂ := by
        simpa [xi_time_part9o_escort_residual_moment_identifiability_moment, a] using hmoment
      nlinarith [ha_pos]
    exact htheta_anti.injective htheta

end

end Omega.Zeta
