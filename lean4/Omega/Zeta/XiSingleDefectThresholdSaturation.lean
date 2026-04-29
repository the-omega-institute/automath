import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
import Omega.Zeta.XiSingleDefectIntegratedClosedForm

namespace Omega.Zeta

/-- Threshold visibility for the single-defect kernel, together with the arctangent saturation
law obtained when the support radius tends to infinity. -/
def xi_single_defect_threshold_saturation_statement
    (D : XiSingleDefectIntegratedClosedFormData) : Prop :=
  (D.ρ ≤ (1 - D.δ) / (1 + D.δ) → D.defectIntegral = 0) ∧
    ((1 - D.δ) / (1 + D.δ) < D.ρ →
      0 < singleDefectSupportRadius D.ρ D.δ ∧
        D.defectIntegral =
          2 * (1 + D.δ) *
              Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 + D.δ)) -
            2 * (1 - D.δ) *
              Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 - D.δ))) ∧
    Filter.Tendsto (fun x : ℝ => D.δ * (4 * Real.arctan x)) Filter.atTop
      (nhds (D.δ * (Real.pi / 2 * 4))) ∧
    D.δ * (Real.pi / 2 * 4) = 2 * Real.pi * D.δ

theorem paper_xi_single_defect_threshold_saturation
    (D : XiSingleDefectIntegratedClosedFormData) :
    xi_single_defect_threshold_saturation_statement D := by
  let A : ℝ := 1 + D.δ
  let B : ℝ := 1 - D.δ
  let R : ℝ :=
    (D.ρ ^ 2 * A ^ 2 - B ^ 2) / (1 - D.ρ ^ 2)
  have hA_pos : 0 < A := by
    dsimp [A]
    linarith [D.hδ.1]
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [D.hδ.2]
  have hden_pos : 0 < 1 - D.ρ ^ 2 := by
    nlinarith [D.hρ.1, D.hρ.2]
  have hclosed := paper_xi_single_defect_integrated_closed_form D
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hthreshold
    have hmul : D.ρ * A ≤ B := by
      have : D.ρ ≤ B / A := by simpa [A, B] using hthreshold
      exact (le_div_iff₀ hA_pos).mp this
    have hρA_nonneg : 0 ≤ D.ρ * A := mul_nonneg D.hρ.1.le hA_pos.le
    have hsq : D.ρ ^ 2 * A ^ 2 ≤ B ^ 2 := by
      have hsq' : (D.ρ * A) ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hρA_nonneg hB_pos.le).2 hmul
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq'
    have hnum_nonpos : D.ρ ^ 2 * A ^ 2 - B ^ 2 ≤ 0 := sub_nonpos.mpr hsq
    have hR_nonpos : R ≤ 0 := by
      dsimp [R]
      exact (div_le_iff₀ hden_pos).2 (by simpa using hnum_nonpos)
    have hradius_zero : singleDefectSupportRadius D.ρ D.δ = 0 := by
      unfold singleDefectSupportRadius
      rw [show
          (D.ρ ^ 2 * (1 + D.δ) ^ 2 - (1 - D.δ) ^ 2) / (1 - D.ρ ^ 2) = R by
            dsimp [R, A, B]]
      rw [max_eq_left hR_nonpos]
      simp
    calc
      D.defectIntegral
          =
            2 * (1 + D.δ) *
                Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 + D.δ)) -
              2 * (1 - D.δ) *
                Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 - D.δ)) := hclosed.2
      _ = 0 := by rw [hradius_zero]; simp
  · intro hthreshold
    have hmul : B < D.ρ * A := by
      have : B / A < D.ρ := by simpa [A, B] using hthreshold
      exact (div_lt_iff₀ hA_pos).mp this
    have hρA_nonneg : 0 ≤ D.ρ * A := mul_nonneg D.hρ.1.le hA_pos.le
    have hsq : B ^ 2 < D.ρ ^ 2 * A ^ 2 := by
      have hsq' : B ^ 2 < (D.ρ * A) ^ 2 := (sq_lt_sq₀ hB_pos.le hρA_nonneg).2 hmul
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq'
    have hnum_pos : 0 < D.ρ ^ 2 * A ^ 2 - B ^ 2 := sub_pos.mpr hsq
    have hR_pos : 0 < R := by
      dsimp [R]
      exact (div_pos_iff.mpr <| Or.inl ⟨hnum_pos, hden_pos⟩)
    have hradius_pos : 0 < singleDefectSupportRadius D.ρ D.δ := by
      unfold singleDefectSupportRadius
      rw [show
          (D.ρ ^ 2 * (1 + D.δ) ^ 2 - (1 - D.δ) ^ 2) / (1 - D.ρ ^ 2) = R by
            dsimp [R, A, B]]
      rw [max_eq_right (le_of_lt hR_pos)]
      exact Real.sqrt_pos.2 hR_pos
    exact ⟨hradius_pos, hclosed.2⟩
  · have hlim :
        Filter.Tendsto (fun x : ℝ => Real.arctan x) Filter.atTop
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) :=
      Real.tendsto_arctan_atTop
    have hlim_nhds :
        Filter.Tendsto (fun x : ℝ => Real.arctan x) Filter.atTop (nhds (Real.pi / 2)) :=
      hlim.mono_right nhdsWithin_le_nhds
    simpa [mul_assoc, mul_left_comm, mul_comm] using hlim_nhds.const_mul (4 * D.δ)
  · ring

end Omega.Zeta
