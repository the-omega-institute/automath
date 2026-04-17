import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Total multiplicity of the defect packets. -/
def xiIndexMass {κ : ℕ} (mass : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j

/-- Defect entropy `S_def = Σ m_j δ_j / (1 + δ_j)`. -/
noncomputable def xiDefectEntropy {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * (δ j / (1 + δ j))

/-- Entropy gap `κ_ind - S_def = Σ m_j / (1 + δ_j)`. -/
noncomputable def xiEntropyGap {κ : ℕ} (mass δ : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j / (1 + δ j)

/-- A finite comoving Fourier model for the nonzero spectral fingerprint. -/
noncomputable def xiComovingFourier {κ : ℕ} (mass δ phase : Fin κ → ℝ) (n : ℕ) : ℝ :=
  4 * Real.pi * Real.exp (-(n : ℝ)) *
    ∑ j, mass j * (δ j / (1 + δ j)) * phase j * Real.exp (-(δ j * (n : ℝ)))

lemma exp_neg_mul_nat_le_inv_one_add (δ : ℝ) (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(δ * (n : ℝ))) ≤ (1 + δ)⁻¹ := by
  have hstep : Real.exp (-(δ * (n : ℝ))) ≤ Real.exp (-δ) := by
    gcongr
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hbase : Real.exp (-δ) ≤ (1 + δ)⁻¹ := by
    have hone : 1 + δ ≤ Real.exp δ := by simpa [add_comm] using Real.add_one_le_exp δ
    have hpos : 0 < 1 + δ := by linarith
    have hexp : 0 < Real.exp δ := Real.exp_pos δ
    have hinv : (Real.exp δ)⁻¹ ≤ (1 + δ)⁻¹ := by
      rwa [inv_le_inv₀ hexp hpos]
    simpa [Real.exp_neg] using hinv
  exact hstep.trans hbase

lemma xiEntropyGap_eq_index_sub_defect {κ : ℕ} (mass δ : Fin κ → ℝ)
    (hδ : ∀ j, 0 < δ j) :
    xiEntropyGap mass δ = xiIndexMass mass - xiDefectEntropy mass δ := by
  unfold xiEntropyGap xiIndexMass xiDefectEntropy
  calc
    ∑ j, mass j / (1 + δ j) = ∑ j, (mass j - mass j * (δ j / (1 + δ j))) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hne : (1 + δ j) ≠ 0 := by linarith [hδ j]
      field_simp [hne]
      ring
    _ = (∑ j, mass j) - ∑ j, mass j * (δ j / (1 + δ j)) := by
      rw [Finset.sum_sub_distrib]
    _ = xiIndexMass mass - xiDefectEntropy mass δ := by
      simp [xiIndexMass, xiDefectEntropy]

/-- Exponential suppression of the nonzero fingerprint by the entropy gap. -/
theorem paper_xi_entropy_gap_exponential_suppression_nonzero_fingerprint {κ : ℕ}
    (mass δ phase : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j) (hδ : ∀ j, 0 < δ j)
    (hphase : ∀ j, |phase j| ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    |xiComovingFourier mass δ phase n| ≤
        4 * Real.pi * Real.exp (-(n : ℝ)) * xiEntropyGap mass δ ∧
      xiEntropyGap mass δ = xiIndexMass mass - xiDefectEntropy mass δ := by
  have hfac_nonneg : 0 ≤ 4 * Real.pi * Real.exp (-(n : ℝ)) := by positivity
  let T : Fin κ → ℝ :=
    fun j => mass j * (δ j / (1 + δ j)) * phase j * Real.exp (-(δ j * (n : ℝ)))
  have hterm :
      ∀ j : Fin κ, |T j| ≤ mass j / (1 + δ j) := by
    intro j
    have hmj : 0 ≤ mass j := hm j
    have hδj : 0 < δ j := hδ j
    have hden_pos : 0 < 1 + δ j := by linarith
    have hfrac_nonneg : 0 ≤ δ j / (1 + δ j) := by positivity
    have hfrac_le_one : δ j / (1 + δ j) ≤ 1 := by
      have hne : (1 + δ j) ≠ 0 := by linarith
      field_simp [hne]
      nlinarith
    have hexp_nonneg : 0 ≤ Real.exp (-(δ j * (n : ℝ))) := by positivity
    have hexp_le : Real.exp (-(δ j * (n : ℝ))) ≤ (1 + δ j)⁻¹ :=
      exp_neg_mul_nat_le_inv_one_add (δ j) hδj hn
    let A : ℝ := mass j * (δ j / (1 + δ j))
    let E : ℝ := Real.exp (-(δ j * (n : ℝ)))
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      positivity
    have hE_nonneg : 0 ≤ E := by
      dsimp [E]
      positivity
    have hA_le : A ≤ mass j := by
      dsimp [A]
      nlinarith
    have hphase_step : A * |phase j| * E ≤ A * 1 * E := by
      have hmul : A * |phase j| ≤ A * 1 := mul_le_mul_of_nonneg_left (hphase j) hA_nonneg
      exact mul_le_mul_of_nonneg_right hmul hE_nonneg
    have hE_step : A * 1 * E ≤ A * 1 * (1 + δ j)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
    have hA_step : A * 1 * (1 + δ j)⁻¹ ≤ mass j * (1 + δ j)⁻¹ := by
      have hA_le' : A * 1 ≤ mass j := by simpa using hA_le
      exact mul_le_mul_of_nonneg_right hA_le' (by positivity)
    calc
      |T j| =
          A * |phase j| * E := by
            dsimp [T]
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hmj, abs_of_nonneg hfrac_nonneg,
              abs_of_nonneg hexp_nonneg]
      _ ≤ A * 1 * E := hphase_step
      _ ≤ A * 1 * (1 + δ j)⁻¹ := hE_step
      _ ≤ mass j * (1 + δ j)⁻¹ := hA_step
      _ = mass j / (1 + δ j) := by
            field_simp [hden_pos.ne']
  have hsum :
      |∑ j, T j| ≤ ∑ j, mass j / (1 + δ j) := by
    calc
      |∑ j, T j| ≤ ∑ j, |T j| := by
            simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := T))
      _ ≤ ∑ j, mass j / (1 + δ j) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact hterm j
  have hbound :
      |xiComovingFourier mass δ phase n| ≤
        4 * Real.pi * Real.exp (-(n : ℝ)) * xiEntropyGap mass δ := by
    unfold xiComovingFourier xiEntropyGap
    calc
      |4 * Real.pi * Real.exp (-(n : ℝ)) * ∑ j, T j| =
          (4 * Real.pi * Real.exp (-(n : ℝ))) * |∑ j, T j| := by
              rw [abs_mul, abs_of_nonneg hfac_nonneg]
      _ ≤ (4 * Real.pi * Real.exp (-(n : ℝ))) * ∑ j, mass j / (1 + δ j) := by
            exact mul_le_mul_of_nonneg_left hsum hfac_nonneg
      _ = 4 * Real.pi * Real.exp (-(n : ℝ)) * xiEntropyGap mass δ := by
            rfl
  exact ⟨hbound, xiEntropyGap_eq_index_sub_defect mass δ hδ⟩

end Omega.Zeta
