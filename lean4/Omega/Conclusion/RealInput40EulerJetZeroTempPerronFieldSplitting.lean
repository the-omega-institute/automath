import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9wBasicRootUnityErrorExponentToOne

namespace Omega.Conclusion

/-- The linear Euler-jet coefficient at the real-input-`40` reference point. -/
noncomputable def conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff :
    ℝ :=
  (((23 : ℝ) - 7 * Real.sqrt 5) / 20)

/-- The quartic zero-temperature Perron polynomial appearing in the conclusion discussion. -/
def conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic (y : ℤ) : ℤ :=
  y ^ 4 - 6 * y ^ 3 + 9 * y ^ 2 - y - 1

/-- A monic quadratic factor with integer coefficients. -/
def conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor
    (a b y : ℤ) : ℤ :=
  y ^ 2 + a * y + b

/-- Paper label: `thm:conclusion-realinput40-euler-jet-zero-temp-perron-field-splitting`. The
audited Euler-jet coefficients lie in `ℚ(√5)`, the first nontrivial jet coefficient is already
non-rational, and the zero-temperature Perron quartic admits no splitting into monic integer
quadratic factors. -/
def conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_statement : Prop :=
  (∃ a₁ b₁ : ℚ,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff =
        (a₁ : ℝ) + (b₁ : ℝ) * Real.sqrt 5) ∧
    (∃ a₂ b₂ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa2 = (a₂ : ℝ) + (b₂ : ℝ) * Real.sqrt 5) ∧
    (∃ a₄ b₄ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa4 = (a₄ : ℝ) + (b₄ : ℝ) * Real.sqrt 5) ∧
    (¬ ∃ q : ℚ,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff = q) ∧
    (¬ ∃ a b c d : ℤ,
      ∀ y : ℤ,
        conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic y =
          conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor a b y *
            conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor c d
              y)

lemma conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff_mem_qsqrt5 :
    ∃ a₁ b₁ : ℚ,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff =
        (a₁ : ℝ) + (b₁ : ℝ) * Real.sqrt 5 := by
  refine ⟨23 / 20, -7 / 20, ?_⟩
  unfold conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff
  ring

lemma conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff_not_rational :
    ¬ ∃ q : ℚ,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff = q := by
  intro hq
  rcases hq with ⟨q, hq⟩
  have hsqrt5 :
      Real.sqrt 5 = ((((23 : ℚ) - 20 * q) / 7 : ℚ) : ℝ) := by
    unfold conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff at hq
    have hsqrt5_real : Real.sqrt 5 = ((23 : ℝ) - 20 * q) / 7 := by
      nlinarith
    simpa using hsqrt5_real
  have hirr : Irrational (Real.sqrt 5) := by
    simpa using (show Nat.Prime 5 by norm_num).irrational_sqrt
  exact hirr.ne_rat _ hsqrt5

lemma conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_kappa2_mem_qsqrt5 :
    ∃ a₂ b₂ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa2 = (a₂ : ℝ) + (b₂ : ℝ) * Real.sqrt 5 := by
  refine ⟨1791 / 200, -(3983 / 1000), ?_⟩
  unfold Omega.Zeta.xiTimePart9wBasicKappa2
  ring_nf

lemma conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_kappa4_mem_qsqrt5 :
    ∃ a₄ b₄ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa4 = (a₄ : ℝ) + (b₄ : ℝ) * Real.sqrt 5 := by
  refine ⟨1354428303 / 100000, -(605718497 / 100000), ?_⟩
  unfold Omega.Zeta.xiTimePart9wBasicKappa4
  ring_nf

lemma conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_no_integer_quadratic_split :
    ¬ ∃ a b c d : ℤ,
      ∀ y : ℤ,
        conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic y =
          conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor a b y *
            conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor c d
              y := by
  rintro ⟨a, b, c, d, hfac⟩
  have h0 : -1 = b * d := by
    simpa [conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor]
      using hfac 0
  have hunit : IsUnit (b * d) := by
    have hminusone : IsUnit (-((1 : ℤ))) := by
      rw [Int.isUnit_iff_abs_eq]
      norm_num
    exact h0.symm ▸ hminusone
  have hbunit : IsUnit b := isUnit_of_mul_isUnit_left (x := b) (y := d) hunit
  have hb_sq : b ^ 2 = 1 := Int.isUnit_sq hbunit
  have hb_cases : b = 1 ∨ b = -1 := by
    have hmul : (b - 1) * (b + 1) = 0 := by
      nlinarith [hb_sq]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hb1 | hb2
    · left
      linarith
    · right
      linarith
  rcases hb_cases with rfl | rfl
  · have hd : d = -1 := by
      have : -1 = (1 : ℤ) * d := by simpa using h0
      linarith
    have h1raw := hfac 1
    norm_num [conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor, hd] at h1raw
    have h1 : 2 = c * (a + 2) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h1raw
    have hneg1raw := hfac (-1)
    norm_num [conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor, hd] at hneg1raw
    have hneg1 : 16 = c * (a - 2) := by
      nlinarith [hneg1raw]
    have hc : (-4 : ℤ) * c = 14 := by
      nlinarith [h1, hneg1]
    omega
  · have hd : d = 1 := by
      have : -1 = (-1 : ℤ) * d := by simpa using h0
      linarith
    have h1raw := hfac 1
    norm_num [conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor, hd] at h1raw
    have h1 : 2 = a * (c + 2) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h1raw
    have hneg1raw := hfac (-1)
    norm_num [conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quartic,
      conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_quadratic_factor, hd] at hneg1raw
    have hneg1 : 16 = a * (c - 2) := by
      nlinarith [hneg1raw]
    have ha : (-4 : ℤ) * a = 14 := by
      nlinarith [h1, hneg1]
    omega

theorem paper_conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting :
    conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_statement := by
  refine ⟨
    conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff_mem_qsqrt5,
    conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_kappa2_mem_qsqrt5,
    conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_kappa4_mem_qsqrt5,
    conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_linear_coeff_not_rational,
    conclusion_realinput40_euler_jet_zero_temp_perron_field_splitting_no_integer_quadratic_split⟩

end Omega.Conclusion
