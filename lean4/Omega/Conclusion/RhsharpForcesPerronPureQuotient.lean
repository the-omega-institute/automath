import Mathlib.Tactic
import Omega.Conclusion.SublinearExcitationFilterInsufficient

namespace Omega.Conclusion

/-- A surviving non-Perron sector in `Sym^b` consumes at most `b - 1` excitations. -/
def conclusion_rhsharp_forces_perron_pure_quotient_nonperron_survives
    (b survivingExcitations : ℕ) : Prop :=
  0 < survivingExcitations ∧ survivingExcitations ≤ b - 1

lemma conclusion_rhsharp_forces_perron_pure_quotient_critical_slope_at_sqrt
    (ρ : ℝ) (hρ : 1 < ρ) : criticalExcitationSlope ρ (Real.sqrt ρ) = 1 := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hsqrt_ne : Real.sqrt ρ ≠ 0 := by positivity
  have hlogρ_ne : Real.log ρ ≠ 0 := by
    have hlogρ_pos : 0 < Real.log ρ := Real.log_pos hρ
    linarith
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := by
    nlinarith [Real.sq_sqrt hρ0.le]
  have hdiv : ρ / Real.sqrt ρ = Real.sqrt ρ := by
    apply (div_eq_iff hsqrt_ne).2
    simpa [mul_comm] using hsq.symm
  unfold criticalExcitationSlope
  rw [hdiv, Real.log_sqrt hρ0.le]
  field_simp [hlogρ_ne]

/-- Paper label: `thm:conclusion-rhsharp-forces-perron-pure-quotient`. -/
theorem paper_conclusion_rhsharp_forces_perron_pure_quotient
    (ρ : ℝ) (hρ : 1 < ρ) (b survivingExcitations : ℕ) (hb : 0 < b) (k_b : ℝ)
    (hLower : criticalExcitationSlope ρ (Real.sqrt ρ) * (b : ℝ) ≤ k_b)
    (hCount : k_b ≤ survivingExcitations) :
    ¬ conclusion_rhsharp_forces_perron_pure_quotient_nonperron_survives
        b survivingExcitations := by
  intro hNonPerron
  rcases hNonPerron with ⟨_, hAvail⟩
  have hSlope :
      criticalExcitationSlope ρ (Real.sqrt ρ) = 1 :=
    conclusion_rhsharp_forces_perron_pure_quotient_critical_slope_at_sqrt ρ hρ
  have hb_le_k : (b : ℝ) ≤ k_b := by
    simpa [hSlope] using hLower
  have hAvail_real : (survivingExcitations : ℝ) ≤ (b - 1 : ℕ) := by
    exact_mod_cast hAvail
  have hlt_nat : b - 1 < b := by
    omega
  have hlt : ((b - 1 : ℕ) : ℝ) < b := by
    exact_mod_cast hlt_nat
  have hle : (b : ℝ) ≤ (b - 1 : ℕ) := le_trans hb_le_k (le_trans hCount hAvail_real)
  exact (not_lt_of_ge hle) hlt

end Omega.Conclusion
