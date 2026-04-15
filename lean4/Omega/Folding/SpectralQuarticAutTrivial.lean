import Mathlib.Tactic

namespace Omega.Folding

/-- Over ℚ, the 7th power has only one real 7th root of unity.
    thm:fold-gauge-anomaly-spectral-quartic-autQ-trivial -/
theorem rat_pow_seven_eq_one_iff (a : ℚ) : a ^ 7 = 1 ↔ a = 1 := by
  constructor
  · intro h
    rcases lt_trichotomy a 1 with hlt | heq | hgt
    · -- a < 1
      rcases lt_trichotomy a 0 with hneg | hzero | hpos
      · -- a < 0 ⇒ a^7 < 0 contradicts a^7 = 1
        have : a ^ 7 < 0 := Odd.pow_neg (by decide) hneg
        linarith
      · -- a = 0 ⇒ a^7 = 0 ≠ 1
        rw [hzero] at h
        norm_num at h
      · -- 0 < a < 1 ⇒ a^7 < 1
        have hlt1 : a ^ 7 < 1 :=
          pow_lt_one₀ hpos.le hlt (by norm_num)
        linarith
    · exact heq
    · -- a > 1 ⇒ a^7 > 1
      have : 1 < a ^ 7 := one_lt_pow₀ hgt (by norm_num)
      linarith
  · intro h; rw [h]; norm_num

/-- In the fixed-case algebraic sub-system, the only ℚ-solution is the
    identity `(a, e) = (1, 1)`.
    thm:fold-gauge-anomaly-spectral-quartic-autQ-trivial -/
theorem rat_fixed_case_forces_identity (a e : ℚ)
    (h1 : e = a ^ 3) (h2 : a * e ^ 2 = 1) :
    a = 1 ∧ e = 1 := by
  have hseven : a ^ 7 = 1 := by
    have hkey : a * e ^ 2 = a ^ 7 := by
      rw [h1]; ring
    linarith [h2, hkey]
  have ha : a = 1 := (rat_pow_seven_eq_one_iff a).mp hseven
  refine ⟨ha, ?_⟩
  rw [h1, ha]
  norm_num

/-- Paper package: Aut_ℚ of the spectral quartic is trivial (algebraic core).
    thm:fold-gauge-anomaly-spectral-quartic-autQ-trivial -/
theorem paper_fold_gauge_anomaly_spectral_quartic_autQ_trivial :
    (∀ a : ℚ, a ^ 7 = 1 ↔ a = 1) ∧
    (∀ (a e : ℚ), e = a ^ 3 → a * e ^ 2 = 1 → a = 1 ∧ e = 1) ∧
    (∀ a : ℚ, a ≠ 1 → a ^ 7 ≠ 1) := by
  refine ⟨rat_pow_seven_eq_one_iff, rat_fixed_case_forces_identity, ?_⟩
  intro a ha heq
  exact ha ((rat_pow_seven_eq_one_iff a).mp heq)

end Omega.Folding
