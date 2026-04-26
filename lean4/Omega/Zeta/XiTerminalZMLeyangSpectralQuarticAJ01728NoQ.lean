import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-leyang-spectral-quartic-a-j-0-1728-noQ`. -/
theorem paper_xi_terminal_zm_leyang_spectral_quartic_a_j_0_1728_noq :
    (¬ ∃ a : ℚ, a ^ 2 - a + 1 = 0) ∧
      (¬ ∃ a : ℚ, 8 * a ^ 3 + 15 * a ^ 2 - 66 * a + 35 = 0) := by
  constructor
  · rintro ⟨a, ha⟩
    nlinarith [sq_nonneg (2 * a - 1)]
  · rintro ⟨a, ha⟩
    have hnumden := a.num_div_den
    rw [← hnumden] at ha
    have hint :
        8 * a.num ^ 3 + 15 * a.num ^ 2 * (a.den : ℤ) -
            66 * a.num * (a.den : ℤ) ^ 2 + 35 * (a.den : ℤ) ^ 3 = 0 := by
      field_simp at ha
      ring_nf at ha
      have hlinear :
          -(a.num * (a.den : ℤ) ^ 2 * 66) + a.num ^ 2 * (a.den : ℤ) * 15 +
              a.num ^ 3 * 8 + (a.den : ℤ) ^ 3 * 35 = 0 := by
        exact_mod_cast ha
      nlinarith
    have hmod :
        8 * (a.num : ZMod 11) ^ 3 + 15 * (a.num : ZMod 11) ^ 2 * (a.den : ZMod 11) -
            66 * (a.num : ZMod 11) * (a.den : ZMod 11) ^ 2 +
              35 * (a.den : ZMod 11) ^ 3 = 0 := by
      have hmodInt := congrArg (fun z : ℤ => (z : ZMod 11)) hint
      norm_num at hmodInt
      ring_nf at hmodInt ⊢
      exact hmodInt
    have hprojective :
        (a.num : ZMod 11) = 0 ∧ (a.den : ZMod 11) = 0 := by
      have hprojective_all :
          ∀ n d : ZMod 11,
            8 * n ^ 3 + 15 * n ^ 2 * d - 66 * n * d ^ 2 + 35 * d ^ 3 = 0 →
              n = 0 ∧ d = 0 := by
        native_decide
      exact hprojective_all (a.num : ZMod 11) (a.den : ZMod 11) hmod
    have h11num : (11 : ℤ) ∣ a.num := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hprojective.1
    have h11den : 11 ∣ a.den := by
      simpa [ZMod.natCast_eq_zero_iff] using hprojective.2
    have h11numNat : 11 ∣ a.num.natAbs := Int.natAbs_dvd_natAbs.mpr h11num
    have hcop := a.reduced
    have hcop11 : Nat.Coprime 11 11 :=
      hcop.coprime_dvd_left h11numNat |>.coprime_dvd_right h11den
    norm_num at hcop11

end Omega.Zeta
