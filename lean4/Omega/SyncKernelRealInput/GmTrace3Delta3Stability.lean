import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

lemma gm_trace3_delta3_stability_cube_defect_identity {m : ℕ} (hm0 : (m : ℝ) ≠ 0)
    (lambda : Fin m → ℝ) (S1 mu : ℝ) (hS1 : S1 = ∑ i, lambda i)
    (hmu : mu = S1 / (m : ℝ)) :
    (∑ i, (lambda i) ^ 3) - S1 ^ 3 / (m : ℝ) ^ 2 =
      ∑ i, (lambda i - mu) ^ 2 * (lambda i + 2 * mu) := by
  have hsum_mu : (∑ i, lambda i) = (m : ℝ) * mu := by
    rw [← hS1, hmu]
    field_simp [hm0]
  have hscaled_sum :
      (∑ i, 3 * mu ^ 2 * lambda i) = 3 * mu ^ 2 * ((m : ℝ) * mu) := by
    rw [← Finset.mul_sum, hsum_mu]
  calc
    (∑ i, (lambda i) ^ 3) - S1 ^ 3 / (m : ℝ) ^ 2 =
        (∑ i, (lambda i) ^ 3) - (m : ℝ) * mu ^ 3 := by
          rw [hS1, hsum_mu]
          field_simp [hm0]
    _ = ∑ i, ((lambda i) ^ 3 - 3 * mu ^ 2 * lambda i + 2 * mu ^ 3) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [hscaled_sum]
          simp
          ring
    _ = ∑ i, (lambda i - mu) ^ 2 * (lambda i + 2 * mu) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring

lemma gm_trace3_delta3_stability_average_le_max {m : ℕ} (hm_pos : 0 < (m : ℝ))
    (lambda : Fin m → ℝ) (lambdaMax S1 : ℝ) (hmax : ∀ i, lambda i ≤ lambdaMax)
    (hS1 : S1 = ∑ i, lambda i) :
    S1 / (m : ℝ) ≤ lambdaMax := by
  have hsum_le : (∑ i, lambda i) ≤ ∑ _i : Fin m, lambdaMax := by
    exact Finset.sum_le_sum fun i _ => hmax i
  have hsum_const : (∑ _i : Fin m, lambdaMax) = (m : ℝ) * lambdaMax := by
    simp
  rw [hS1]
  rw [hsum_const] at hsum_le
  rw [div_le_iff₀ hm_pos]
  nlinarith

lemma gm_trace3_delta3_stability_defect_ge_cube {m : ℕ} (hm_pos : 0 < (m : ℝ))
    (lambda : Fin m → ℝ) (h_nonneg : ∀ i, 0 ≤ lambda i)
    (lambdaMax S1 mu Delta3 : ℝ) (hmax : ∀ i, lambda i ≤ lambdaMax)
    (h_hasmax : ∃ i, lambdaMax = lambda i) (hS1 : S1 = ∑ i, lambda i)
    (hmu : mu = S1 / (m : ℝ))
    (hDelta : Delta3 = (∑ i, (lambda i) ^ 3) - S1 ^ 3 / (m : ℝ) ^ 2) :
    (lambdaMax - mu) ^ 3 ≤ Delta3 := by
  rcases h_hasmax with ⟨i0, hi0⟩
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hmu_nonneg : 0 ≤ mu := by
    have hsum_nonneg : 0 ≤ ∑ i, lambda i := Finset.sum_nonneg fun i _ => h_nonneg i
    rw [hmu, hS1]
    positivity
  have hmax_nonneg : 0 ≤ lambdaMax := by
    rw [hi0]
    exact h_nonneg i0
  have hdiff_nonneg : 0 ≤ lambdaMax - mu := by
    have havg_le :=
      gm_trace3_delta3_stability_average_le_max hm_pos lambda lambdaMax S1 hmax hS1
    rw [hmu]
    exact sub_nonneg.mpr havg_le
  have hDelta_sum :
      Delta3 = ∑ i, (lambda i - mu) ^ 2 * (lambda i + 2 * mu) := by
    rw [hDelta]
    exact gm_trace3_delta3_stability_cube_defect_identity hm0 lambda S1 mu hS1 hmu
  have hsummand_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ (lambda i - mu) ^ 2 * (lambda i + 2 * mu) := by
    intro i _
    exact mul_nonneg (sq_nonneg _) (by nlinarith [h_nonneg i, hmu_nonneg])
  have hterm_le_sum :
      (lambda i0 - mu) ^ 2 * (lambda i0 + 2 * mu) ≤
        ∑ i, (lambda i - mu) ^ 2 * (lambda i + 2 * mu) := by
    exact Finset.single_le_sum hsummand_nonneg (by simp)
  have hterm_le_delta :
      (lambdaMax - mu) ^ 2 * (lambdaMax + 2 * mu) ≤ Delta3 := by
    rw [hDelta_sum]
    simpa [hi0] using hterm_le_sum
  have hcube_le_term :
      (lambdaMax - mu) ^ 3 ≤ (lambdaMax - mu) ^ 2 * (lambdaMax + 2 * mu) := by
    have hfactor : lambdaMax - mu ≤ lambdaMax + 2 * mu := by nlinarith [hmu_nonneg]
    have hsquare : 0 ≤ (lambdaMax - mu) ^ 2 := sq_nonneg _
    calc
      (lambdaMax - mu) ^ 3 = (lambdaMax - mu) ^ 2 * (lambdaMax - mu) := by ring
      _ ≤ (lambdaMax - mu) ^ 2 * (lambdaMax + 2 * mu) :=
        mul_le_mul_of_nonneg_left hfactor hsquare
  exact hcube_le_term.trans hterm_le_delta

/-- Paper label: `prop:gm-trace3-delta3-stability`. For a nonnegative finite spectrum, the
third trace defect controls the excess of the maximum eigenvalue above the mean. -/
theorem paper_gm_trace3_delta3_stability {m : ℕ} (hm : 3 ≤ m) (lambda : Fin m → ℝ)
    (h_nonneg : ∀ i, 0 ≤ lambda i) :
    ∃ c_m : ℝ, 0 ≤ c_m ∧
      ∀ lambdaMax S1 mu Delta3 C : ℝ,
        (∀ i, lambda i ≤ lambdaMax) →
          (∃ i, lambdaMax = lambda i) →
            S1 = ∑ i, lambda i →
              mu = S1 / (m : ℝ) →
                Delta3 = (∑ i, (lambda i) ^ 3) - S1 ^ 3 / (m : ℝ) ^ 2 →
                  0 ≤ C → C ^ 3 = Delta3 → lambdaMax ≤ mu + c_m * C := by
  refine ⟨1, by norm_num, ?_⟩
  intro lambdaMax S1 mu Delta3 C hmax h_hasmax hS1 hmu hDelta hC_nonneg hC_cube
  have hm_nat_pos : 0 < m := by omega
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_nat_pos
  have hcube_le :
      (lambdaMax - mu) ^ 3 ≤ C ^ 3 := by
    rw [hC_cube]
    exact gm_trace3_delta3_stability_defect_ge_cube hm_pos lambda h_nonneg
      lambdaMax S1 mu Delta3 hmax h_hasmax hS1 hmu hDelta
  have hdiff_nonneg : 0 ≤ lambdaMax - mu := by
    have havg_le :=
      gm_trace3_delta3_stability_average_le_max hm_pos lambda lambdaMax S1 hmax hS1
    rw [hmu]
    exact sub_nonneg.mpr havg_le
  have hdiff_le_C : lambdaMax - mu ≤ C := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hC_nonneg hcube_le
  nlinarith

end

end Omega.SyncKernelRealInput
