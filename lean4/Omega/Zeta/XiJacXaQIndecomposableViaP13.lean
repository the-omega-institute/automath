import Mathlib.Tactic

namespace Omega.Zeta

/-- The local factor used at `p = 13`. -/
def xi_jac_xa_q_indecomposable_via_p13_local_factor (T : ℚ) : ℚ :=
  169 * T ^ 4 - 2 * T ^ 2 + 1

/-- The even quadratic-in-`T^2` factor has negative discriminant. -/
lemma xi_jac_xa_q_indecomposable_via_p13_even_discriminant_nonsquare :
    ¬ ∃ u : ℚ, 169 * u ^ 2 - 2 * u + 1 = 0 := by
  rintro ⟨u, hu⟩
  have hs : 0 ≤ (169 * u - 1) ^ 2 := sq_nonneg (169 * u - 1)
  have hzero : (169 * u - 1) ^ 2 + 168 = 0 := by
    nlinarith
  nlinarith

/-- The odd-term cancellation case would force the impossible rational square `a^2 = 28`. -/
lemma xi_jac_xa_q_indecomposable_via_p13_no_rational_square_twenty_eight :
    ¬ ∃ a : ℚ, a ^ 2 = 28 := by
  rintro ⟨a, ha⟩
  have haq := a.num_div_den
  rw [← haq] at ha
  have hnumden : a.num ^ 2 = 28 * (a.den : ℤ) ^ 2 := by
    have hden_ne : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_ne_zero
    field_simp [hden_ne] at ha
    ring_nf at ha
    have h_int :
        (((a.num ^ 2 : ℤ) : ℚ) = ((28 * (a.den : ℤ) ^ 2 : ℤ) : ℚ)) := by
      push_cast
      nlinarith
    exact_mod_cast h_int
  have h7num2 : (7 : ℤ) ∣ a.num ^ 2 := ⟨4 * (a.den : ℤ) ^ 2, by rw [hnumden]; ring⟩
  have h7num : (7 : ℤ) ∣ a.num := Prime.dvd_of_dvd_pow (by decide) h7num2
  have h7_num_nat : 7 ∣ a.num.natAbs := Int.natAbs_dvd_natAbs.mpr h7num
  obtain ⟨k, hk⟩ := h7num
  have h7den2 : (7 : ℤ) ∣ (a.den : ℤ) ^ 2 := by
    rw [hk] at hnumden
    have : 7 * k ^ 2 = 4 * (a.den : ℤ) ^ 2 := by nlinarith
    have h7_left : (7 : ℤ) ∣ 4 * (a.den : ℤ) ^ 2 := ⟨k ^ 2, by linarith⟩
    rcases (Prime.dvd_or_dvd (by decide : Prime (7 : ℤ)) h7_left) with h74 | h7d2
    · norm_num at h74
    · exact h7d2
  have h7den : (7 : ℤ) ∣ (a.den : ℤ) := Prime.dvd_of_dvd_pow (by decide) h7den2
  have h7_den_nat : 7 ∣ a.den := by exact_mod_cast h7den
  have hnot_coprime : ¬ a.num.natAbs.Coprime a.den := by
    intro hc
    exact absurd
      (show (7 : ℕ) ∣ 1 from
        hc.coprime_dvd_left h7_num_nat |>.coprime_dvd_right h7_den_nat |>.symm ▸
          dvd_refl 7)
      (by omega)
  exact hnot_coprime a.reduced

/-- No product of two elliptic local quadratic factors gives the displayed local factor. -/
lemma xi_jac_xa_q_indecomposable_via_p13_no_elliptic_quadratic_product :
    ¬ ∃ a b : ℚ, ∀ T : ℚ,
      xi_jac_xa_q_indecomposable_via_p13_local_factor T =
        (1 - a * T + 13 * T ^ 2) * (1 - b * T + 13 * T ^ 2) := by
  rintro ⟨a, b, hprod⟩
  have h1 := hprod 1
  have hm1 := hprod (-1)
  have h2 := hprod 2
  have hsum : a + b = 0 := by
    unfold xi_jac_xa_q_indecomposable_via_p13_local_factor at h1 hm1
    ring_nf at h1 hm1
    nlinarith
  have hab : a * b = -28 := by
    unfold xi_jac_xa_q_indecomposable_via_p13_local_factor at h2
    ring_nf at h2
    nlinarith
  have hsquare : a ^ 2 = 28 := by
    have hb : b = -a := by linarith
    rw [hb] at hab
    nlinarith
  exact xi_jac_xa_q_indecomposable_via_p13_no_rational_square_twenty_eight ⟨a, hsquare⟩

/-- Paper-facing obstruction statement for the `p = 13` local factor. -/
def xi_jac_xa_q_indecomposable_via_p13_statement : Prop :=
  (xi_jac_xa_q_indecomposable_via_p13_local_factor = fun T : ℚ =>
    169 * T ^ 4 - 2 * T ^ 2 + 1) ∧
  (¬ ∃ u : ℚ, 169 * u ^ 2 - 2 * u + 1 = 0) ∧
  (¬ ∃ a : ℚ, a ^ 2 = 28) ∧
  (¬ ∃ a b : ℚ, ∀ T : ℚ,
    xi_jac_xa_q_indecomposable_via_p13_local_factor T =
      (1 - a * T + 13 * T ^ 2) * (1 - b * T + 13 * T ^ 2))

/-- Paper label: `thm:xi-jac-xa-q-indecomposable-via-p13`. -/
theorem paper_xi_jac_xa_q_indecomposable_via_p13 :
    xi_jac_xa_q_indecomposable_via_p13_statement := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact xi_jac_xa_q_indecomposable_via_p13_even_discriminant_nonsquare
  · exact xi_jac_xa_q_indecomposable_via_p13_no_rational_square_twenty_eight
  · exact xi_jac_xa_q_indecomposable_via_p13_no_elliptic_quadratic_product

end Omega.Zeta
