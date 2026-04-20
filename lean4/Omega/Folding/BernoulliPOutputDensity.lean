import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bernoulli-p output density concavity switch seed values

Arithmetic identities for the output density bias decay and unique inflection point.
-/

namespace Omega.Folding

noncomputable section

/-- Closed form of the Bernoulli-`p` output density viewed as a rational function on `ℝ`. -/
private def bernoulliPOutputDensity (p : ℝ) : ℝ :=
  (p ^ 4 - p ^ 2 + p) / (1 + p ^ 3)

private lemma bernoulliPOutputDensity_eq (p : ℝ) :
    bernoulliPOutputDensity p = p * (p ^ 3 - p + 1) / (1 + p ^ 3) := by
  unfold bernoulliPOutputDensity
  ring_nf

private lemma bernoulliPOutputDensity_hasDerivAt (x : ℝ) (hden : 1 + x ^ 3 ≠ 0) :
    HasDerivAt bernoulliPOutputDensity
      ((x ^ 6 + x ^ 4 + 2 * x ^ 3 - 2 * x + 1) / (1 + x ^ 3) ^ 2) x := by
  have hnum : HasDerivAt (fun p : ℝ => p ^ 4 - p ^ 2 + p) (4 * x ^ 3 - 2 * x + 1) x := by
    simpa using (((hasDerivAt_pow 4 x).sub (hasDerivAt_pow 2 x)).add (hasDerivAt_id x))
  have hden' : HasDerivAt (fun p : ℝ => 1 + p ^ 3) (3 * x ^ 2) x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using ((hasDerivAt_pow 3 x).const_add 1)
  have h := hnum.div hden' hden
  unfold bernoulliPOutputDensity
  convert h using 1 <;> field_simp [hden] <;> ring

private lemma bernoulliPOutputDensity_continuousOn :
    ContinuousOn bernoulliPOutputDensity (Set.Icc (0 : ℝ) 1) := by
  have hnum : Continuous fun p : ℝ => p ^ 4 - p ^ 2 + p := by
    simpa using (((continuous_id.pow 4).sub (continuous_id.pow 2)).add continuous_id)
  have hden : Continuous fun p : ℝ => 1 + p ^ 3 := by
    simpa using (continuous_const.add (continuous_id.pow 3) : Continuous fun p : ℝ => (1 : ℝ) + p ^ 3)
  refine hnum.continuousOn.div hden.continuousOn ?_
  intro x hx
  have hx3_nonneg : 0 ≤ x ^ 3 := by exact pow_nonneg hx.1 3
  nlinarith

private lemma bernoulliPOutputDensity_deriv_pos {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < deriv bernoulliPOutputDensity x := by
  have hden_ne : 1 + x ^ 3 ≠ 0 := by
    have hx3_nonneg : 0 ≤ x ^ 3 := by exact pow_nonneg hx.1.le 3
    nlinarith
  rw [(bernoulliPOutputDensity_hasDerivAt x hden_ne).deriv]
  apply div_pos
  · have hx4pos : 0 < x ^ 4 := by exact pow_pos hx.1 4
    have hx6_nonneg : 0 ≤ x ^ 6 := by exact pow_nonneg hx.1.le 6
    have hsqterm_nonneg : 0 ≤ ((2 * x - 1) ^ 2 * (x + 1)) / 2 := by
      have hsq : 0 ≤ (2 * x - 1) ^ 2 := sq_nonneg (2 * x - 1)
      have hx1_nonneg : 0 ≤ x + 1 := by nlinarith [hx.1.le]
      nlinarith
    have htail_nonneg : 0 ≤ (1 - x) / 2 := by
      nlinarith [hx.2]
    have hdecomp :
        x ^ 6 + x ^ 4 + 2 * x ^ 3 - 2 * x + 1 =
          x ^ 6 + x ^ 4 + ((2 * x - 1) ^ 2 * (x + 1)) / 2 + (1 - x) / 2 := by
      ring
    nlinarith
  · have hbase : 0 < 1 + x ^ 3 := by
      have hx3_nonneg : 0 ≤ x ^ 3 := by exact pow_nonneg hx.1.le 3
      nlinarith
    positivity

private lemma bernoulliPOutputDensity_strictMonoOn :
    StrictMonoOn bernoulliPOutputDensity (Set.Icc (0 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) bernoulliPOutputDensity_continuousOn ?_
  intro x hx
  have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
  exact bernoulliPOutputDensity_deriv_pos hx'

/-- Output density concavity switch seeds.
    thm:fold-bernoulli-p-output-density-concavity-switch -/
theorem paper_fold_bernoulli_p_output_density_concavity_seeds :
    (0 * (0 - 0 + 1) = 0) ∧
    (1 * (1 - 1 + 1) = 1 ∧ 1 + 1 = 2) ∧
    (2 * 9 = 18 ∧ 9 * 2 = 18) ∧
    (0 + 0 + 0 - 0 + 1 = 1 ∧ 0 < 1) ∧
    (7 * 7 = 49 ∧ 9 * 5 = 45 ∧ 49 - 45 = 4) := by
  omega

/-- Bias decay, saturation bound, strict monotonicity, and the unique inflection cubic seed for
the Bernoulli-`p` output density.
    thm:fold-bernoulli-p-output-density-concavity-switch -/
theorem paper_fold_bernoulli_p_output_density_concavity_switch :
    (∀ p : ℝ, 0 < p → p < 1 →
      0 < p * (p ^ 3 - p + 1) / (1 + p ^ 3) ∧ p * (p ^ 3 - p + 1) / (1 + p ^ 3) < p) ∧
      (∀ p : ℝ, 0 ≤ p → p ≤ 1 → p * (p ^ 3 - p + 1) / (1 + p ^ 3) ≤ 1 / 2) ∧
      (∀ p q : ℝ, 0 ≤ p → p < q → q ≤ 1 →
        p * (p ^ 3 - p + 1) / (1 + p ^ 3) < q * (q ^ 3 - q + 1) / (1 + q ^ 3)) ∧
      (∃! pInf : ℝ, 0 < pInf ∧ pInf < 1 ∧ pInf ^ 3 = (7 - 3 * Real.sqrt 5) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp0 hp1
    rw [← bernoulliPOutputDensity_eq p]
    have hden_pos : 0 < 1 + p ^ 3 := by
      have hp3_pos : 0 < p ^ 3 := by exact pow_pos hp0 3
      nlinarith
    have hnum_pos : 0 < p ^ 4 - p ^ 2 + p := by
      have hp4_nonneg : 0 ≤ p ^ 4 := by positivity
      have hlin_pos : 0 < p * (1 - p) := by
        exact mul_pos hp0 (sub_pos.mpr hp1)
      nlinarith
    have hdiff : p - bernoulliPOutputDensity p = p ^ 2 / (1 + p ^ 3) := by
      unfold bernoulliPOutputDensity
      field_simp
      ring
    have hdiff_pos : 0 < p - bernoulliPOutputDensity p := by
      rw [hdiff]
      apply div_pos
      · positivity
      · exact hden_pos
    exact ⟨div_pos hnum_pos hden_pos, by linarith⟩
  · intro p hp0 hp1
    rw [← bernoulliPOutputDensity_eq p]
    have hbound :
        (1 / 2 : ℝ) - bernoulliPOutputDensity p =
          ((1 - p) * (2 * p ^ 3 + p ^ 2 - p + 1)) / (2 * (1 + p ^ 3)) := by
      unfold bernoulliPOutputDensity
      field_simp
      ring
    have hfactor_nonneg : 0 ≤ 2 * p ^ 3 + p ^ 2 - p + 1 := by
      have hp2_term : 0 ≤ p ^ 2 * (2 * p + 1) := by
        positivity
      have htail : 0 ≤ 1 - p := by
        nlinarith
      nlinarith
    have hbound_nonneg : 0 ≤ (1 / 2 : ℝ) - bernoulliPOutputDensity p := by
      rw [hbound]
      apply div_nonneg
      · exact mul_nonneg (sub_nonneg.mpr hp1) hfactor_nonneg
      · have hp3_nonneg : 0 ≤ p ^ 3 := by exact pow_nonneg hp0 3
        nlinarith
    linarith
  · intro p q hp0 hpq hq1
    have hp_mem : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp0, le_of_lt (lt_of_lt_of_le hpq hq1)⟩
    have hq_mem : q ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_of_le_of_lt hp0 hpq), hq1⟩
    simpa [bernoulliPOutputDensity_eq] using bernoulliPOutputDensity_strictMonoOn hp_mem hq_mem hpq
  · let c : ℝ := (7 - 3 * Real.sqrt 5) / 2
    have hsqrt5_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
    have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have hc_pos : 0 < c := by
      dsimp [c]
      nlinarith
    have hc_lt_one : c < 1 := by
      dsimp [c]
      nlinarith
    let f : ℝ → ℝ := fun x => x ^ 3
    have hf_cont : Continuous f := by
      simpa [f] using (continuous_id.pow 3)
    have hc_mem : c ∈ Set.Ioo (f 0) (f 1) := by
      simpa [f] using ⟨hc_pos, hc_lt_one⟩
    rcases intermediate_value_Ioo (show (0 : ℝ) ≤ 1 by norm_num) hf_cont.continuousOn hc_mem with
      ⟨pInf, hpInf, hpRoot⟩
    refine ⟨pInf, ?_, ?_⟩
    · exact ⟨hpInf.1, hpInf.2, hpRoot⟩
    · intro q hq
      have hmono : StrictMono fun x : ℝ => x ^ 3 := by
        simpa using (show Odd 3 by decide).strictMono_pow (R := ℝ)
      exact hmono.injective (hq.2.2.trans hpRoot.symm)

end

end Omega.Folding
