import Mathlib.Tactic
import Omega.Conclusion.SublinearExcitationFilterInsufficient

namespace Omega.Conclusion

lemma conclusion_finite_state_selector_cannot_sustain_kernel_rh_selector_bound
    (stateCount : ℕ) (selector : ℕ → Fin stateCount) (b : ℕ) :
    ((selector b : ℕ) : ℝ) ≤ stateCount := by
  exact_mod_cast Nat.le_of_lt (selector b).2

/-- Paper label: `cor:conclusion-finite-state-selector-cannot-sustain-kernel-rh`. A selector that
takes only finitely many values yields a uniform bound on the excitation count. Any positive
critical slope then turns that bounded count into an eventually subcritical filter, so the
selector cannot keep the kernel-RH condition true at arbitrarily large orders. -/
theorem paper_conclusion_finite_state_selector_cannot_sustain_kernel_rh
    (rho eta : ℝ) (hRho : 1 < rho) (hEta0 : 0 < eta) (hEtaLt : eta < rho)
    (hSlopePos : 0 < criticalExcitationSlope rho eta)
    (stateCount : ℕ) (selector : ℕ → Fin stateCount) (kernelRH : ℕ → Prop)
    (hNecessaryLower :
      ∀ b, 2 ≤ b → kernelRH b → criticalExcitationSlope rho eta * b ≤ ((selector b : ℕ) : ℝ)) :
    ∃ N : ℕ, ∀ b ≥ N, ¬ kernelRH b := by
  have hStatePos : 0 < stateCount := by
    exact lt_of_le_of_lt (Nat.zero_le _) (selector 0).2
  let c : ℝ := criticalExcitationSlope rho eta / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    linarith
  have hSubcritical : c < criticalExcitationSlope rho eta := by
    dsimp [c]
    linarith
  have hEventuallyUpper :
      ∃ N : ℕ, ∀ b ≥ N, ((selector b : ℕ) : ℝ) ≤ c * b := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (stateCount : ℝ) / c < N := exists_nat_gt ((stateCount : ℝ) / c)
    refine ⟨max N 2, ?_⟩
    intro b hb
    have hbN : N ≤ b := le_trans (Nat.le_max_left _ _) hb
    have hb_real : (N : ℝ) ≤ b := by exact_mod_cast hbN
    have hratio_lt : (stateCount : ℝ) / c < b := lt_of_lt_of_le hN hb_real
    have hstate_lt : (stateCount : ℝ) < c * b := by
      have hratio_mul : c * ((stateCount : ℝ) / c) < c * b :=
        mul_lt_mul_of_pos_left hratio_lt hc_pos
      simpa [div_eq_mul_inv, hc_pos.ne', mul_assoc, mul_comm, mul_left_comm] using hratio_mul
    have hselector_le :
        ((selector b : ℕ) : ℝ) ≤ stateCount :=
      conclusion_finite_state_selector_cannot_sustain_kernel_rh_selector_bound
        stateCount selector b
    linarith
  let D : SublinearExcitationFilterData :=
    { rho := rho
      eta := eta
      hRho := hRho
      hEta0 := hEta0
      hEtaLt := hEtaLt
      k := fun b => ((selector b : ℕ) : ℝ)
      kernelRH := kernelRH
      c := c
      hSubcritical := hSubcritical
      hEventuallyUpper := hEventuallyUpper
      hNecessaryLower := hNecessaryLower }
  simpa [D, SublinearExcitationFilterData.sublinearFiltersFailEventually] using
    paper_conclusion_sublinear_excitation_filter_insufficient D

end Omega.Conclusion
