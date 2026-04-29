import Mathlib

namespace Omega.Conclusion

open Filter

/-- The normalized dyadic counting scale `2^{m q}`. -/
noncomputable def conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale
    (q m : ℕ) : ℝ :=
  (2 : ℝ) ^ (m * q)

/-- The target `q`-dimensional volume scale `2^{-m (n - q)}`. -/
noncomputable def conclusion_boundary_dimension_lifting_necessary_tax_volume_scale
    (n q m : ℕ) : ℝ :=
  ((2 : ℝ) ^ (m * (n - q)))⁻¹

/-- The outer approximation volume profile obtained from the normalized counting function. -/
noncomputable def conclusion_boundary_dimension_lifting_necessary_tax_outer_volume
    (n q : ℕ) (countA : ℕ → ℝ) (m : ℕ) : ℝ :=
  conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m *
    (countA m / conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale q m)

/-- Boundary Lipschitz scale written so that dividing by it recovers the `2^{m(q-1)}` tax. -/
noncomputable def conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale
    (n q m : ℕ) : ℝ :=
  conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m /
    conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale (q - 1) m

lemma conclusion_boundary_dimension_lifting_necessary_tax_volume_scale_ne_zero
    (n q m : ℕ) :
    conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m ≠ 0 := by
  unfold conclusion_boundary_dimension_lifting_necessary_tax_volume_scale
  positivity

lemma conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale_ne_zero (q m : ℕ) :
    conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale q m ≠ 0 := by
  unfold conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale
  positivity

/-- Paper label: `thm:conclusion-boundary-dimension-lifting-necessary-tax`.

If the dyadic outer approximation has `o(2^{m q})` counting growth, while a competing approximation
still carries `q`-dimensional volume `c 2^{-m (n-q)}` and the SPG boundary-distance inequality
controls volume discrepancy by the boundary scale, then the boundary distance must pay the
universal lifting tax `Ω(2^{m (q-1)})`. -/
theorem paper_conclusion_boundary_dimension_lifting_necessary_tax
    (n q : ℕ) (c : ℝ) (countA volV Dist_m : ℕ → ℝ)
    (hq : 1 ≤ q) (hc : 0 < c)
    (hCountNonneg : ∀ m, 0 ≤ countA m)
    (hCount :
      Tendsto
        (fun m =>
          countA m / conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale q m)
        atTop (nhds 0))
    (hLower :
      ∀ᶠ m in atTop,
        c * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m ≤ volV m)
    (hLipschitz :
      ∀ m,
        |volV m -
            conclusion_boundary_dimension_lifting_necessary_tax_outer_volume n q countA m| ≤
          conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale n q m * Dist_m m)
    (hDistNonneg : ∀ m, 0 ≤ Dist_m m) :
    Tendsto
        (fun m =>
          conclusion_boundary_dimension_lifting_necessary_tax_outer_volume n q countA m /
            conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m)
        atTop (nhds 0) ∧
      ∀ᶠ m in atTop,
        (c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale (q - 1) m ≤
          Dist_m m := by
  let _ := hq
  let _ := hDistNonneg
  have hOuter :
      Tendsto
          (fun m =>
            conclusion_boundary_dimension_lifting_necessary_tax_outer_volume n q countA m /
              conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m)
          atTop (nhds 0) := by
    refine Tendsto.congr' ?_ hCount
    filter_upwards with m
    have hscale_ne :=
      conclusion_boundary_dimension_lifting_necessary_tax_volume_scale_ne_zero n q m
    simp [conclusion_boundary_dimension_lifting_necessary_tax_outer_volume, hscale_ne]
  have hc_half : 0 < c / 2 := by positivity
  have hSmall :
      ∀ᶠ m in atTop,
        countA m / conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale q m <
          c / 2 := by
    have hMem : Set.Ioo (-(c / 2)) (c / 2) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith [hc_half]) hc_half
    have hEventually :
        ∀ᶠ m in atTop,
          countA m / conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale q m ∈
            Set.Ioo (-(c / 2)) (c / 2) := hCount hMem
    filter_upwards [hEventually] with m hm
    exact hm.2
  refine ⟨hOuter, ?_⟩
  filter_upwards [hLower, hSmall] with m hmLower hmSmall
  have hBulk_pos :
      0 < conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale q m := by
    unfold conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale
    positivity
  have hVolume_pos :
      0 < conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m := by
    unfold conclusion_boundary_dimension_lifting_necessary_tax_volume_scale
    positivity
  have hBoundary_pos :
      0 < conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale n q m := by
    have hBulk_prev_pos :
        0 < conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale (q - 1) m := by
      unfold conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale
      positivity
    unfold conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale
    exact div_pos hVolume_pos hBulk_prev_pos
  have hNormalized_nonneg :
      0 ≤ countA m / conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale q m := by
    exact div_nonneg (hCountNonneg m) hBulk_pos.le
  have hOuter_le :
      conclusion_boundary_dimension_lifting_necessary_tax_outer_volume n q countA m ≤
        (c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m := by
    unfold conclusion_boundary_dimension_lifting_necessary_tax_outer_volume
    have hmul :=
      mul_le_mul_of_nonneg_left (le_of_lt hmSmall) hVolume_pos.le
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hGap_nonneg :
      0 ≤
        volV m - conclusion_boundary_dimension_lifting_necessary_tax_outer_volume n q countA m := by
    have hHalf_le :
        (c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m ≤
          c * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m := by
      nlinarith [hc, hVolume_pos]
    exact sub_nonneg.mpr (le_trans (le_trans hOuter_le hHalf_le) hmLower)
  have hGap_lower :
      (c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m ≤
        |volV m - conclusion_boundary_dimension_lifting_necessary_tax_outer_volume n q countA m| := by
    rw [abs_of_nonneg hGap_nonneg]
    linarith
  have hGap_upper :
      (c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m ≤
        conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale n q m * Dist_m m := by
    exact le_trans hGap_lower (hLipschitz m)
  have hTax :
      ((c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m) /
          conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale n q m ≤
        Dist_m m := by
    rw [div_le_iff₀ hBoundary_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hGap_upper
  have hRatio :
      ((c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_volume_scale n q m) /
          conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale n q m =
        (c / 2) * conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale (q - 1) m := by
    have hVolume_ne :=
      conclusion_boundary_dimension_lifting_necessary_tax_volume_scale_ne_zero n q m
    have hBulk_ne :=
      conclusion_boundary_dimension_lifting_necessary_tax_bulk_scale_ne_zero (q - 1) m
    unfold conclusion_boundary_dimension_lifting_necessary_tax_boundary_scale
    field_simp [hVolume_ne, hBulk_ne]
  simpa [hRatio] using hTax

end Omega.Conclusion
