import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Conclusion.XiDyadicShellEnvelopeLaw

namespace Omega.Conclusion

/-- Dyadic decay weight used for the explicit Xi-tail model. -/
noncomputable def xiDyadicWeight (K : ℕ) : ℝ :=
  ((2 ^ K : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) * Real.exp (-Real.pi * 2 ^ K)

/-- Dyadic block added at scale `2^K`. -/
noncomputable def xiDyadicBlock (z : ℂ) (K : ℕ) : ℂ :=
  -((z ^ 2) + (1 / 4 : ℂ)) * (xiDyadicWeight K : ℂ)

/-- Dyadic partial sums. -/
noncomputable def xiDyadicPartial (z : ℂ) (K : ℕ) : ℂ :=
  1 / 2 + ∑ k ∈ Finset.range K, xiDyadicBlock z k

/-- Explicit superexponential tail constant from the paper. -/
noncomputable def xiDyadicTailConstant : ℝ :=
  1 / (Real.pi * (1 - Real.exp (-3 * Real.pi)))

/-- Dyadic completion model: partial sum plus one explicit superexponential tail term. -/
noncomputable def xiDyadicCompletion (z : ℂ) (K : ℕ) : ℂ :=
  xiDyadicPartial z K + (xiDyadicTailConstant : ℂ) * (-((z ^ 2) + (1 / 4 : ℂ))) *
    (xiDyadicWeight K : ℂ)

private lemma xiDyadicTailConstant_nonneg : 0 ≤ xiDyadicTailConstant := by
  unfold xiDyadicTailConstant
  have hden : 0 < Real.pi * (1 - Real.exp (-3 * Real.pi)) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hexp : Real.exp (-3 * Real.pi) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos]
    have hone : 0 < 1 - Real.exp (-3 * Real.pi) := by linarith
    exact mul_pos hpi hone
  exact le_of_lt (one_div_pos.mpr hden)

private lemma xiDyadicPartial_succ (z : ℂ) (K : ℕ) :
    xiDyadicPartial z (K + 1) = xiDyadicPartial z K + xiDyadicBlock z K := by
  unfold xiDyadicPartial
  rw [Finset.sum_range_succ]
  ring

private lemma norm_sq_quarter_le (z : ℂ) : ‖-((z ^ 2) + (1 / 4 : ℂ))‖ ≤ ‖z‖ ^ 2 + 1 := by
  calc
    ‖-((z ^ 2) + (1 / 4 : ℂ))‖ = ‖(z ^ 2) + (1 / 4 : ℂ)‖ := by rw [norm_neg]
    _ ≤ ‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ ^ 2 + 1 / 4 := by
          rw [norm_pow]
          norm_num
    _ ≤ ‖z‖ ^ 2 + 1 := by nlinarith

private lemma xiDyadicWeight_nonneg (K : ℕ) : 0 ≤ xiDyadicWeight K := by
  unfold xiDyadicWeight
  positivity

private lemma xiDyadicWeight_le_strip (K : ℕ) {η : ℝ} (hη0 : 0 ≤ η) :
    xiDyadicWeight K ≤
      ((2 ^ K : ℕ) : ℝ) ^ (-(3 / 4 : ℝ) + η / 2) * Real.exp (-Real.pi * 2 ^ K) := by
  have hbase : 1 ≤ ((2 ^ K : ℕ) : ℝ) := by
    have hpow : (1 : ℕ) ≤ 2 ^ K := by
      exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) K)
    exact_mod_cast hpow
  have hpow :
      ((2 ^ K : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤
        ((2 ^ K : ℕ) : ℝ) ^ (-(3 / 4 : ℝ) + η / 2) := by
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  unfold xiDyadicWeight
  gcongr

private lemma real_norm_sq_quarter_le (t : ℝ) :
    ‖-((((t : ℂ) ^ 2) + (1 / 4 : ℂ)) )‖ ≤ t ^ 2 + 1 := by
  simpa using norm_sq_quarter_le (t : ℂ)

private lemma xiDyadicCompletion_sub_partial_real (t : ℝ) (K : ℕ) :
    xiDyadicCompletion (t : ℂ) K - xiDyadicPartial (t : ℂ) K =
      (xiDyadicTailConstant : ℂ) * (-((((t : ℂ) ^ 2) + (1 / 4 : ℂ))) : ℂ) *
        (xiDyadicWeight K : ℂ) := by
  simp [xiDyadicCompletion, sub_eq_add_neg, add_left_comm, add_comm]

private lemma xiDyadicCompletion_sub_partial (z : ℂ) (K : ℕ) :
    xiDyadicCompletion z K - xiDyadicPartial z K =
      (xiDyadicTailConstant : ℂ) * (-((z ^ 2) + (1 / 4 : ℂ))) * (xiDyadicWeight K : ℂ) := by
  simp [xiDyadicCompletion, sub_eq_add_neg, add_left_comm, add_comm]

private lemma conclusion_xi_dyadic_depth_law_tail_constant_pos :
    0 < xiDyadicTailConstant := by
  unfold xiDyadicTailConstant
  have hden : 0 < Real.pi * (1 - Real.exp (-3 * Real.pi)) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hexp : Real.exp (-3 * Real.pi) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos]
    have hone : 0 < 1 - Real.exp (-3 * Real.pi) := by linarith
    exact mul_pos hpi hone
  exact one_div_pos.mpr hden

private lemma conclusion_xi_dyadic_depth_law_weight_le_exp (K : ℕ) :
    xiDyadicWeight K ≤ Real.exp (-Real.pi * 2 ^ K) := by
  let x : ℝ := ((2 ^ K : ℕ) : ℝ)
  have hx1 : 1 ≤ x := by
    have hpow : (1 : ℕ) ≤ 2 ^ K := by
      exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) K)
    change (1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ)
    exact_mod_cast hpow
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hpow : 1 ≤ x ^ (3 / 4 : ℝ) := Real.one_le_rpow hx1 (by positivity)
  have hfac : x ^ (-(3 / 4 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hx0]
    simpa [one_div] using inv_le_one_of_one_le₀ hpow
  unfold xiDyadicWeight
  calc
    x ^ (-(3 / 4 : ℝ)) * Real.exp (-Real.pi * 2 ^ K) ≤
        1 * Real.exp (-Real.pi * 2 ^ K) := by
          exact mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = Real.exp (-Real.pi * 2 ^ K) := by ring

/-- Dyadic recursion plus explicit real-axis and strip superexponential bounds for the concrete
Xi-completion model.
    thm:conclusion-xi-dyadic-recursion-superexp -/
theorem paper_conclusion_xi_dyadic_recursion_superexp
    (t : ℝ) (z : ℂ) (K : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (_hη1 : η ≤ 1) (_hstrip : |z.im| ≤ η) :
    xiDyadicPartial z (K + 1) = xiDyadicPartial z K + xiDyadicBlock z K ∧
      ‖xiDyadicCompletion (t : ℂ) K - xiDyadicPartial (t : ℂ) K‖ ≤
        xiDyadicTailConstant * (t ^ 2 + 1) * xiDyadicWeight K ∧
      ‖xiDyadicCompletion z K - xiDyadicPartial z K‖ ≤
        xiDyadicTailConstant * (‖z‖ ^ 2 + 1) *
          (((2 ^ K : ℕ) : ℝ) ^ (-(3 / 4 : ℝ) + η / 2) * Real.exp (-Real.pi * 2 ^ K)) := by
  refine ⟨xiDyadicPartial_succ z K, ?_, ?_⟩
  · rw [xiDyadicCompletion_sub_partial_real]
    calc
      ‖(xiDyadicTailConstant : ℂ) * (-((((t : ℂ) ^ 2) + (1 / 4 : ℂ))) : ℂ) *
          (xiDyadicWeight K : ℂ)‖
        = xiDyadicTailConstant * ‖-((((t : ℂ) ^ 2) + (1 / 4 : ℂ)) : ℂ)‖ * xiDyadicWeight K := by
            rw [norm_mul, norm_mul]
            simp [abs_of_nonneg, xiDyadicTailConstant_nonneg, xiDyadicWeight_nonneg]
      _ ≤ xiDyadicTailConstant * (t ^ 2 + 1) * xiDyadicWeight K := by
            have hmid :
                xiDyadicTailConstant * (‖-((((t : ℂ) ^ 2) + (1 / 4 : ℂ)) : ℂ)‖ * xiDyadicWeight K) ≤
                  xiDyadicTailConstant * ((t ^ 2 + 1) * xiDyadicWeight K) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (real_norm_sq_quarter_le t) (xiDyadicWeight_nonneg K))
                xiDyadicTailConstant_nonneg
            simpa [mul_assoc] using hmid
  · rw [xiDyadicCompletion_sub_partial]
    calc
      ‖(xiDyadicTailConstant : ℂ) * (-((z ^ 2) + (1 / 4 : ℂ))) * (xiDyadicWeight K : ℂ)‖
        = xiDyadicTailConstant * ‖-((z ^ 2) + (1 / 4 : ℂ))‖ * xiDyadicWeight K := by
            rw [norm_mul, norm_mul]
            simp [abs_of_nonneg, xiDyadicTailConstant_nonneg, xiDyadicWeight_nonneg]
      _ ≤ xiDyadicTailConstant * (‖z‖ ^ 2 + 1) * xiDyadicWeight K := by
            have hmid :
                xiDyadicTailConstant * (‖-((z ^ 2) + (1 / 4 : ℂ))‖ * xiDyadicWeight K) ≤
                  xiDyadicTailConstant * ((‖z‖ ^ 2 + 1) * xiDyadicWeight K) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (norm_sq_quarter_le z) (xiDyadicWeight_nonneg K))
                xiDyadicTailConstant_nonneg
            simpa [mul_assoc] using hmid
      _ ≤ xiDyadicTailConstant * (‖z‖ ^ 2 + 1) *
          (((2 ^ K : ℕ) : ℝ) ^ (-(3 / 4 : ℝ) + η / 2) * Real.exp (-Real.pi * 2 ^ K)) := by
            have hfac_nonneg : 0 ≤ xiDyadicTailConstant * (‖z‖ ^ 2 + 1) := by
              exact mul_nonneg xiDyadicTailConstant_nonneg (by positivity)
            exact mul_le_mul_of_nonneg_left (xiDyadicWeight_le_strip K hη0) hfac_nonneg

/-- Paper label: `cor:conclusion-xi-dyadic-depth-law`. On the real axis, once `2^K` passes the
explicit logarithmic threshold, the dyadic tail is bounded by `ε`. -/
theorem paper_conclusion_xi_dyadic_depth_law
    (t ε : ℝ) (K : ℕ) (hε0 : 0 < ε) (_hε1 : ε ≤ 1)
    (hK :
      ((2 ^ K : ℕ) : ℝ) ≥
        (1 / Real.pi) * Real.log (xiDyadicTailConstant * (t ^ 2 + 1) / ε)) :
    ‖xiDyadicCompletion (t : ℂ) K - xiDyadicPartial (t : ℂ) K‖ ≤ ε := by
  have hsuper :=
    paper_conclusion_xi_dyadic_recursion_superexp (t := t) (z := (t : ℂ)) (K := K) (η := 0)
      (hη0 := le_rfl) (_hη1 := by norm_num) (_hstrip := by simp)
  rcases hsuper with ⟨_, hreal, _⟩
  have htail :
      ‖xiDyadicCompletion (t : ℂ) K - xiDyadicPartial (t : ℂ) K‖ ≤
        xiDyadicTailConstant * (t ^ 2 + 1) * Real.exp (-Real.pi * 2 ^ K) := by
    calc
      ‖xiDyadicCompletion (t : ℂ) K - xiDyadicPartial (t : ℂ) K‖ ≤
          xiDyadicTailConstant * (t ^ 2 + 1) * xiDyadicWeight K := hreal
      _ ≤ xiDyadicTailConstant * (t ^ 2 + 1) * Real.exp (-Real.pi * 2 ^ K) := by
          have hfac_nonneg : 0 ≤ xiDyadicTailConstant * (t ^ 2 + 1) := by
            exact mul_nonneg xiDyadicTailConstant_nonneg (by positivity)
          exact mul_le_mul_of_nonneg_left
            (conclusion_xi_dyadic_depth_law_weight_le_exp K) hfac_nonneg
  have hdiv_pos : 0 < xiDyadicTailConstant * (t ^ 2 + 1) / ε := by
    refine div_pos ?_ hε0
    exact mul_pos conclusion_xi_dyadic_depth_law_tail_constant_pos (by positivity)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_ne : (Real.pi : ℝ) ≠ 0 := ne_of_gt hpi_pos
  have hlog_le : Real.log (xiDyadicTailConstant * (t ^ 2 + 1) / ε) ≤ Real.pi * 2 ^ K := by
    have hmul :
        Real.pi * ((1 / Real.pi) * Real.log (xiDyadicTailConstant * (t ^ 2 + 1) / ε)) ≤
          Real.pi * (((2 ^ K : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hK hpi_pos.le
    simpa [div_eq_mul_inv, mul_assoc, hpi_ne] using hmul
  have hexp_le :
      xiDyadicTailConstant * (t ^ 2 + 1) / ε ≤ Real.exp (Real.pi * 2 ^ K) := by
    have := Real.exp_le_exp.2 hlog_le
    simpa [Real.exp_log hdiv_pos] using this
  have hscaled :
      (xiDyadicTailConstant * (t ^ 2 + 1) / ε) * Real.exp (-Real.pi * 2 ^ K) ≤ 1 := by
    have htmp := mul_le_mul_of_nonneg_right hexp_le (by positivity : 0 ≤ Real.exp (-Real.pi * 2 ^ K))
    simpa [mul_assoc, ← Real.exp_add, add_comm, add_left_comm, add_assoc] using htmp
  have hmain :
      xiDyadicTailConstant * (t ^ 2 + 1) * Real.exp (-Real.pi * 2 ^ K) ≤ ε := by
    have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hε0
    calc
      xiDyadicTailConstant * (t ^ 2 + 1) * Real.exp (-Real.pi * 2 ^ K) =
          ε * ((xiDyadicTailConstant * (t ^ 2 + 1) / ε) * Real.exp (-Real.pi * 2 ^ K)) := by
            field_simp [hεne]
      _ ≤ ε * 1 := by
            exact mul_le_mul_of_nonneg_left hscaled hε0.le
      _ = ε := by ring
  exact htail.trans hmain

noncomputable section

/-- The explicit dyadic shell envelope used in the Rouché shift estimate. -/
def conclusion_xi_rouche_stability_dyadicEnvelope (K : ℕ) : ℝ :=
  (2 / Real.pi) * (2 : ℝ) ^ (-(3 / 4 : ℝ) * (K : ℝ)) *
    Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ))

/-- Concrete Rouché stability package for a simple zero and its dyadic truncations. -/
structure conclusion_xi_rouche_stability_data where
  z0 : ℂ
  truncatedZero : ℕ → ℂ
  K0 : ℕ
  radius : ℝ
  boundaryMargin : ℝ
  t0 : ℝ
  boundaryError : ℕ → ℝ
  shell : ℕ → ℝ → ℝ
  radius_pos : 0 < radius
  boundaryMargin_pos : 0 < boundaryMargin
  rouche_unique :
    ∀ K : ℕ, K0 ≤ K →
      ‖truncatedZero K - z0‖ < radius ∧
        ∀ z : ℂ, ‖z - z0‖ < radius → z = truncatedZero K
  rouche_shift :
    ∀ K : ℕ, K0 ≤ K →
      ‖truncatedZero K - z0‖ ≤ radius / boundaryMargin * boundaryError K
  boundaryError_le_shell :
    ∀ K : ℕ, K0 ≤ K → boundaryError K ≤ |shell K t0|
  shell_formula :
    ∀ K t,
      shell K t =
        (2 / Real.pi) * (2 : ℝ) ^ (-(3 / 4 : ℝ) * (K : ℝ)) *
            Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ)) *
          Real.cos (((K : ℝ) * Real.log 2 / 2) * t)

namespace conclusion_xi_rouche_stability_data

/-- Rouché gives a unique truncated zero in the isolating disk. -/
def uniqueTruncatedZero (D : conclusion_xi_rouche_stability_data) : Prop :=
  ∀ K : ℕ, D.K0 ≤ K →
    ‖D.truncatedZero K - D.z0‖ < D.radius ∧
      ∀ z : ℂ, ‖z - D.z0‖ < D.radius → z = D.truncatedZero K

/-- The abstract Rouché/shift-control inequality before inserting the dyadic envelope. -/
def shiftBound (D : conclusion_xi_rouche_stability_data) : Prop :=
  ∀ K : ℕ, D.K0 ≤ K →
    ‖D.truncatedZero K - D.z0‖ ≤ D.radius / D.boundaryMargin * D.boundaryError K

/-- The explicit superexponential dyadic shift bound. -/
def explicitSuperexpShiftBound (D : conclusion_xi_rouche_stability_data) : Prop :=
  ∀ K : ℕ, D.K0 ≤ K →
    ‖D.truncatedZero K - D.z0‖ ≤
      D.radius / D.boundaryMargin * conclusion_xi_rouche_stability_dyadicEnvelope K

end conclusion_xi_rouche_stability_data

open conclusion_xi_rouche_stability_data

/-- Paper label: `thm:conclusion-xi-rouche-stability`. -/
theorem paper_conclusion_xi_rouche_stability (D : conclusion_xi_rouche_stability_data) :
    D.uniqueTruncatedZero ∧ D.shiftBound ∧ D.explicitSuperexpShiftBound := by
  refine ⟨D.rouche_unique, D.rouche_shift, ?_⟩
  intro K hK
  have hshell := paper_conclusion_xi_dyadic_shell_envelope_law D.shell D.shell_formula
  have htail :
      D.boundaryError K ≤ conclusion_xi_rouche_stability_dyadicEnvelope K := by
    exact (D.boundaryError_le_shell K hK).trans (by
      simpa [conclusion_xi_rouche_stability_dyadicEnvelope] using (hshell K D.t0).1)
  have hfactor_nonneg : 0 ≤ D.radius / D.boundaryMargin :=
    div_nonneg (le_of_lt D.radius_pos) (le_of_lt D.boundaryMargin_pos)
  exact (D.rouche_shift K hK).trans (mul_le_mul_of_nonneg_left htail hfactor_nonneg)

end

end Omega.Conclusion
