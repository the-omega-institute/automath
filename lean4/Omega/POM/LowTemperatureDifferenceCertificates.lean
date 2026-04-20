import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-low-temperature-difference-certificates`. -/
theorem paper_pom_low_temperature_difference_certificates (P : ℕ → ℝ) (alpha h gap C : ℝ)
    (q0 : ℕ) (hgap : 0 ≤ gap)
    (happrox :
      ∀ q ≥ q0, |P q - ((q : ℝ) * alpha + h)| ≤ C * Real.exp (-gap * (q : ℝ))) :
    ∃ C' : ℝ, ∃ q1 : ℕ, 1 ≤ q1 ∧
      ∀ q ≥ q1,
        |(P (q + 1) - P q) - alpha| ≤ C' * Real.exp (-gap * (q : ℝ)) ∧
          |(P q - (q : ℝ) * (P (q + 1) - P q)) - h|
            ≤ C' * (q : ℝ) * Real.exp (-gap * (q : ℝ)) ∧
          |P (q + 1) - 2 * P q + P (q - 1)| ≤ C' * Real.exp (-gap * (q : ℝ)) := by
  let R : ℕ → ℝ := fun q => P q - ((q : ℝ) * alpha + h)
  let E : ℕ → ℝ := fun q => Real.exp (-gap * (q : ℝ))
  let C' : ℝ := (3 + Real.exp gap) * C
  have hR : ∀ q ≥ q0, |R q| ≤ C * E q := by
    intro q hq
    simpa [R, E] using happrox q hq
  have hC_nonneg : 0 ≤ C := by
    have h0 := hR q0 (le_rfl)
    have hE0_pos : 0 < E q0 := by
      simp [E, Real.exp_pos]
    have hCE0_nonneg : 0 ≤ C * E q0 := le_trans (abs_nonneg _) h0
    nlinarith
  refine ⟨C', q0 + 1, by omega, ?_⟩
  intro q hq
  have hq0 : q ≥ q0 := by omega
  have hq1 : q + 1 ≥ q0 := by omega
  have hqm1 : q - 1 ≥ q0 := by omega
  have hq_ge_one : 1 ≤ q := by omega
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hq_real_ge_one : (1 : ℝ) ≤ q := by exact_mod_cast hq_ge_one
  have hEq_succ : E (q + 1) ≤ E q := by
    dsimp [E]
    have hq_succ : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by norm_num
    rw [hq_succ]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hq_pred : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_pred hq_ge_one]
  have hEq_pred : E (q - 1) = Real.exp gap * E q := by
    dsimp [E]
    rw [hq_pred]
    calc
      Real.exp (-gap * ((q : ℝ) - 1)) = Real.exp (gap + -gap * (q : ℝ)) := by ring_nf
      _ = Real.exp gap * Real.exp (-gap * (q : ℝ)) := by rw [Real.exp_add]
  have hRq := hR q hq0
  have hRq1 := hR (q + 1) hq1
  have hRqm1 := hR (q - 1) hqm1
  have hEq_nonneg : 0 ≤ E q := le_of_lt (by simp [E, Real.exp_pos])
  have hdiffR : |R (q + 1) - R q| ≤ 2 * C * E q := by
    have hstep1 : |R (q + 1) - R q| ≤ |R (q + 1)| + |R q| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (R (q + 1)) (-R q)
    have hstep2 : |R (q + 1)| + |R q| ≤ C * E (q + 1) + C * E q := by
      linarith
    have hstep3 : C * E (q + 1) ≤ C * E q := by
      exact mul_le_mul_of_nonneg_left hEq_succ hC_nonneg
    have hstep4 : C * E (q + 1) + C * E q ≤ 2 * C * E q := by
      nlinarith
    exact hstep1.trans (hstep2.trans hstep4)
  have hdiffPred : |R q - R (q - 1)| ≤ C * (1 + Real.exp gap) * E q := by
    calc
      |R q - R (q - 1)| ≤ |R q| + |R (q - 1)| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (R q) (-R (q - 1))
      _ ≤ C * E q + C * E (q - 1) := by linarith
      _ = C * E q + C * (Real.exp gap * E q) := by rw [hEq_pred]
      _ = C * (1 + Real.exp gap) * E q := by ring
  have hq_succ : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by norm_num
  have hfirst_eq : (P (q + 1) - P q) - alpha = R (q + 1) - R q := by
    dsimp [R]
    rw [hq_succ]
    ring
  have hintercept_eq :
      (P q - (q : ℝ) * (P (q + 1) - P q)) - h = R q - (q : ℝ) * (R (q + 1) - R q) := by
    dsimp [R]
    rw [hq_succ]
    ring
  have hsecond_eq :
      P (q + 1) - 2 * P q + P (q - 1) = (R (q + 1) - R q) - (R q - R (q - 1)) := by
    dsimp [R]
    rw [hq_succ, hq_pred]
    ring
  have hcoeff_first : 2 * C ≤ C' := by
    dsimp [C']
    nlinarith [Real.exp_pos gap]
  have hcoeff_intercept : 3 * C ≤ C' := by
    dsimp [C']
    nlinarith [Real.exp_pos gap]
  have hcoeff_second : 2 * C + C * (1 + Real.exp gap) ≤ C' := by
    dsimp [C']
    nlinarith [Real.exp_pos gap]
  refine ⟨?_, ?_, ?_⟩
  · calc
      |(P (q + 1) - P q) - alpha| = |R (q + 1) - R q| := by rw [hfirst_eq]
      _ ≤ 2 * C * E q := hdiffR
      _ ≤ C' * E q := mul_le_mul_of_nonneg_right hcoeff_first hEq_nonneg
  · have hmul_diff : (q : ℝ) * |R (q + 1) - R q| ≤ (q : ℝ) * (2 * C * E q) := by
      exact mul_le_mul_of_nonneg_left hdiffR hq_nonneg
    have hRq_to_q : C * E q ≤ C * (q : ℝ) * E q := by
      have hCE_nonneg : 0 ≤ C * E q := mul_nonneg hC_nonneg hEq_nonneg
      calc
        C * E q = 1 * (C * E q) := by ring
        _ ≤ (q : ℝ) * (C * E q) := mul_le_mul_of_nonneg_right hq_real_ge_one hCE_nonneg
        _ = C * (q : ℝ) * E q := by ring
    calc
      |(P q - (q : ℝ) * (P (q + 1) - P q)) - h| = |R q - (q : ℝ) * (R (q + 1) - R q)| := by
        rw [hintercept_eq]
      _ ≤ |R q| + |(q : ℝ) * (R (q + 1) - R q)| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (R q) (-(q : ℝ) * (R (q + 1) - R q))
      _ = |R q| + (q : ℝ) * |R (q + 1) - R q| := by
        rw [abs_mul, abs_of_nonneg hq_nonneg]
      _ ≤ C * E q + (q : ℝ) * (2 * C * E q) := by linarith
      _ ≤ 3 * C * (q : ℝ) * E q := by
        nlinarith
      _ ≤ C' * (q : ℝ) * E q := by
        have hqE_nonneg : 0 ≤ (q : ℝ) * E q := mul_nonneg hq_nonneg hEq_nonneg
        have hmul := mul_le_mul_of_nonneg_right hcoeff_intercept hqE_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  · calc
      |P (q + 1) - 2 * P q + P (q - 1)| = |(R (q + 1) - R q) - (R q - R (q - 1))| := by
        rw [hsecond_eq]
      _ ≤ |R (q + 1) - R q| + |R (q - 1) - R q| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (R (q + 1) - R q) (-(R q - R (q - 1)))
      _ = |R (q + 1) - R q| + |R q - R (q - 1)| := by
        rw [abs_sub_comm (R (q - 1)) (R q)]
      _ ≤ 2 * C * E q + C * (1 + Real.exp gap) * E q := by
        linarith
      _ = (2 * C + C * (1 + Real.exp gap)) * E q := by ring
      _ ≤ C' * E q := mul_le_mul_of_nonneg_right hcoeff_second hEq_nonneg

end Omega.POM
