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

lemma xiDefectEntropy_nonneg {κ : ℕ} (mass δ : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j)
    (hδ : ∀ j, 0 < δ j) : 0 ≤ xiDefectEntropy mass δ := by
  unfold xiDefectEntropy
  refine Finset.sum_nonneg ?_
  intro j hj
  have hfrac_nonneg : 0 ≤ δ j / (1 + δ j) := by
    have hden_pos : 0 < 1 + δ j := by linarith [hδ j]
    exact div_nonneg (le_of_lt (hδ j)) hden_pos.le
  exact mul_nonneg (hm j) hfrac_nonneg

lemma xi_weighted_square_lower_bound {κ : ℕ} (mass w : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j) :
    (∑ j, mass j * w j) ^ 2 ≤ xiIndexMass mass * ∑ j, mass j * (w j) ^ 2 := by
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (fun j => Real.sqrt (mass j) * w j)
      (fun j => Real.sqrt (mass j))
  have hleft :
      (∑ j, (Real.sqrt (mass j) * w j) * Real.sqrt (mass j)) = ∑ j, mass j * w j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hsqrt : Real.sqrt (mass j) * Real.sqrt (mass j) = mass j := by
      nlinarith [Real.sq_sqrt (hm j)]
    calc
      (Real.sqrt (mass j) * w j) * Real.sqrt (mass j) =
          (Real.sqrt (mass j) * Real.sqrt (mass j)) * w j := by ring
      _ = mass j * w j := by rw [hsqrt]
  have hsq :
      (∑ j, (Real.sqrt (mass j) * w j) ^ 2) = ∑ j, mass j * (w j) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hsqrt : Real.sqrt (mass j) * Real.sqrt (mass j) = mass j := by
      nlinarith [Real.sq_sqrt (hm j)]
    calc
      (Real.sqrt (mass j) * w j) ^ 2 = (Real.sqrt (mass j) * Real.sqrt (mass j)) * (w j) ^ 2 := by
        ring
      _ = mass j * (w j) ^ 2 := by rw [hsqrt]
  have hmass :
      (∑ j, (Real.sqrt (mass j)) ^ 2) = xiIndexMass mass := by
    unfold xiIndexMass
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact Real.sq_sqrt (hm j)
  rw [hleft, hsq, hmass] at hcs
  simpa [mul_comm] using hcs

lemma xi_weighted_gap_product_bound {κ : ℕ} (mass w : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j)
    (hmass_pos : 0 < xiIndexMass mass) :
    ∑ j, mass j * (w j * (1 - w j)) ≤
      (∑ j, mass j * w j) * (xiIndexMass mass - ∑ j, mass j * w j) / xiIndexMass mass := by
  set S : ℝ := ∑ j, mass j * w j
  set Q : ℝ := ∑ j, mass j * (w j) ^ 2
  have hsq : S ^ 2 ≤ xiIndexMass mass * Q := by
    simpa [S, Q] using xi_weighted_square_lower_bound mass w hm
  have hQ : S ^ 2 / xiIndexMass mass ≤ Q := by
    apply (div_le_iff₀ hmass_pos).2
    simpa [mul_comm] using hsq
  have hdecomp : ∑ j, mass j * (w j * (1 - w j)) = S - Q := by
    calc
      ∑ j, mass j * (w j * (1 - w j)) = ∑ j, (mass j * w j - mass j * w j ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = (∑ j, mass j * w j) - ∑ j, mass j * w j ^ 2 := by rw [Finset.sum_sub_distrib]
      _ = S - Q := by simp [S, Q]
  have hmass_ne : xiIndexMass mass ≠ 0 := ne_of_gt hmass_pos
  calc
    ∑ j, mass j * (w j * (1 - w j)) = S - Q := hdecomp
    _ ≤ S - S ^ 2 / xiIndexMass mass := by linarith
    _ = S * (xiIndexMass mass - S) / xiIndexMass mass := by
      field_simp [hmass_ne]

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

theorem paper_xi_nonzero_harmonic_entropy_gap_product_sharp {κ : ℕ}
    (mass δ phase : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j) (hδ : ∀ j, 0 < δ j)
    (hphase : ∀ j, |phase j| ≤ 1) (hmass_pos : 0 < xiIndexMass mass) {n : ℕ} (hn : 1 ≤ n) :
    |xiComovingFourier mass δ phase n| ≤
      4 * Real.pi * Real.exp (-(n : ℝ)) *
        (xiDefectEntropy mass δ * (xiIndexMass mass - xiDefectEntropy mass δ) /
          xiIndexMass mass) := by
  have hfac_nonneg : 0 ≤ 4 * Real.pi * Real.exp (-(n : ℝ)) := by positivity
  let w : Fin κ → ℝ := fun j => δ j / (1 + δ j)
  let T : Fin κ → ℝ :=
    fun j => mass j * w j * phase j * Real.exp (-(δ j * (n : ℝ)))
  have hw : ∀ j, 0 ≤ w j ∧ w j ≤ 1 := by
    intro j
    constructor
    · have hden_pos : 0 < 1 + δ j := by linarith [hδ j]
      dsimp [w]
      exact div_nonneg (le_of_lt (hδ j)) hden_pos.le
    · have hden_pos : 0 < 1 + δ j := by linarith [hδ j]
      dsimp [w]
      exact (div_le_iff₀ hden_pos).2 (by linarith [hδ j])
  have hterm :
      ∀ j : Fin κ, |T j| ≤ mass j * (w j * (1 - w j)) := by
    intro j
    have hmj : 0 ≤ mass j := hm j
    have hwj_nonneg : 0 ≤ w j := (hw j).1
    have hwj_le_one : w j ≤ 1 := (hw j).2
    have hexp_nonneg : 0 ≤ Real.exp (-(δ j * (n : ℝ))) := by positivity
    have hexp_le : Real.exp (-(δ j * (n : ℝ))) ≤ 1 - w j := by
      have hbase := exp_neg_mul_nat_le_inv_one_add (δ j) (hδ j) hn
      have hw_compl : 1 - w j = (1 + δ j)⁻¹ := by
        dsimp [w]
        have hden_ne : (1 + δ j) ≠ 0 := by linarith [hδ j]
        field_simp [hden_ne]
        ring
      rw [hw_compl]
      exact hbase
    let A : ℝ := mass j * w j
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      positivity
    have hphase_step : A * |phase j| * Real.exp (-(δ j * (n : ℝ))) ≤ A * Real.exp (-(δ j * (n : ℝ))) := by
      have hmul : A * |phase j| ≤ A * 1 := mul_le_mul_of_nonneg_left (hphase j) hA_nonneg
      simpa using mul_le_mul_of_nonneg_right hmul hexp_nonneg
    have hexp_step : A * Real.exp (-(δ j * (n : ℝ))) ≤ A * (1 - w j) := by
      simpa [A] using mul_le_mul_of_nonneg_left hexp_le hA_nonneg
    calc
      |T j| = A * |phase j| * Real.exp (-(δ j * (n : ℝ))) := by
        dsimp [T, A]
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hmj, abs_of_nonneg hwj_nonneg,
          abs_of_nonneg hexp_nonneg]
      _ ≤ A * Real.exp (-(δ j * (n : ℝ))) := hphase_step
      _ ≤ A * (1 - w j) := hexp_step
      _ = mass j * (w j * (1 - w j)) := by
        dsimp [A]
        ring
  have hsum :
      |∑ j, T j| ≤ ∑ j, mass j * (w j * (1 - w j)) := by
    calc
      |∑ j, T j| ≤ ∑ j, |T j| := by
        simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := T))
      _ ≤ ∑ j, mass j * (w j * (1 - w j)) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact hterm j
  have hmix :
      ∑ j, mass j * (w j * (1 - w j)) ≤
        xiDefectEntropy mass δ * (xiIndexMass mass - xiDefectEntropy mass δ) / xiIndexMass mass := by
    have hgap :=
      xi_weighted_gap_product_bound mass w hm hmass_pos
    simpa [w, xiDefectEntropy] using hgap
  unfold xiComovingFourier
  calc
    |4 * Real.pi * Real.exp (-(n : ℝ)) * ∑ j, T j| =
        (4 * Real.pi * Real.exp (-(n : ℝ))) * |∑ j, T j| := by
          rw [abs_mul, abs_of_nonneg hfac_nonneg]
    _ ≤ (4 * Real.pi * Real.exp (-(n : ℝ))) * ∑ j, mass j * (w j * (1 - w j)) := by
          exact mul_le_mul_of_nonneg_left hsum hfac_nonneg
    _ ≤ (4 * Real.pi * Real.exp (-(n : ℝ))) *
          (xiDefectEntropy mass δ * (xiIndexMass mass - xiDefectEntropy mass δ) /
            xiIndexMass mass) := by
          exact mul_le_mul_of_nonneg_left hmix hfac_nonneg

theorem paper_xi_entropy_gap_lower_bound_from_two_samples {κ : ℕ}
    (mass δ phase : Fin κ → ℝ) (u0 : ℝ) (hm : ∀ j, 0 ≤ mass j) (hδ : ∀ j, 0 < δ j)
    (hphase : ∀ j, |phase j| ≤ 1) (hmass_pos : 0 < xiIndexMass mass) {n : ℕ} (hn : 1 ≤ n)
    (hu0 : u0 = 4 * Real.pi * xiDefectEntropy mass δ) (hu0nz : u0 ≠ 0) :
    xiIndexMass mass - xiDefectEntropy mass δ ≥
      xiIndexMass mass * Real.exp (n : ℝ) * |xiComovingFourier mass δ phase n| / |u0| := by
  have hdef_nonneg : 0 ≤ xiDefectEntropy mass δ := xiDefectEntropy_nonneg mass δ hm hδ
  have hu0abs : |u0| = 4 * Real.pi * xiDefectEntropy mass δ := by
    rw [hu0, abs_of_nonneg]
    positivity
  have hu0pos : 0 < |u0| := abs_pos.mpr hu0nz
  have hdef_pos : 0 < xiDefectEntropy mass δ := by
    have hpi : 0 < 4 * Real.pi := by positivity
    rw [hu0abs] at hu0pos
    exact (mul_pos_iff_of_pos_left hpi).mp hu0pos
  have hmul :=
    mul_le_mul_of_nonneg_left
      (paper_xi_nonzero_harmonic_entropy_gap_product_sharp mass δ phase hm hδ hphase hmass_pos hn)
      (by positivity : 0 ≤ xiIndexMass mass * Real.exp (n : ℝ) / |u0|)
  have hmass_ne : xiIndexMass mass ≠ 0 := ne_of_gt hmass_pos
  have hdef_ne : xiDefectEntropy mass δ ≠ 0 := ne_of_gt hdef_pos
  have hexp_cancel : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hrewrite :
      (xiIndexMass mass * Real.exp (n : ℝ) / |u0|) *
          (4 * Real.pi * Real.exp (-(n : ℝ)) *
            (xiDefectEntropy mass δ * (xiIndexMass mass - xiDefectEntropy mass δ) /
              xiIndexMass mass)) =
        xiIndexMass mass - xiDefectEntropy mass δ := by
    rw [hu0abs, div_eq_mul_inv]
    field_simp [hmass_ne, hdef_ne]
    rw [hexp_cancel]
    ring
  have hleft :
      (xiIndexMass mass * Real.exp (n : ℝ) / |u0|) * |xiComovingFourier mass δ phase n| =
        xiIndexMass mass * Real.exp (n : ℝ) * |xiComovingFourier mass δ phase n| / |u0| := by
    ring_nf
  calc
    xiIndexMass mass * Real.exp (n : ℝ) * |xiComovingFourier mass δ phase n| / |u0|
        = (xiIndexMass mass * Real.exp (n : ℝ) / |u0|) * |xiComovingFourier mass δ phase n| := by
            symm
            exact hleft
    _ ≤ xiIndexMass mass - xiDefectEntropy mass δ := by
      rw [hrewrite] at hmul
      exact hmul

end Omega.Zeta
