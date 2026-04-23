import Mathlib

namespace Omega.Conclusion

open Filter

/-- The dyadic boundary scale `2^{m(d-1)}` appearing in the renormalization tax. -/
noncomputable def conclusion_boundary_content_renormalization_necessary_tax_scale
    (d m : ℕ) : ℝ :=
  (2 : ℝ) ^ (m * (d - 1))

/-- The volume discrepancy after subtracting the two leading asymptotic terms. -/
noncomputable def conclusion_boundary_content_renormalization_necessary_tax_residual
    (gap : ℕ → ℝ) (mainTerm boundaryTerm : ℝ) (d m : ℕ) : ℝ :=
  |gap m - mainTerm * (2 : ℝ) ^ (m * d) -
      boundaryTerm * conclusion_boundary_content_renormalization_necessary_tax_scale d m|

/-- If the renormalized residual gap is eventually bounded below by a positive constant while the
SPG Lipschitz estimate bounds it above by `2^{-m(d-1)} / (α₁ + 1)` times the distance, then the
distance must pay the complementary dyadic tax `Ω(2^{m(d-1)})`. -/
def conclusion_boundary_content_renormalization_necessary_tax_statement : Prop :=
  ∀ (d α1 : ℕ) (mainTerm boundaryTerm c : ℝ),
    0 < c →
    ∀ (gap dist : ℕ → ℝ),
      (∀ᶠ m in atTop,
          c ≤ conclusion_boundary_content_renormalization_necessary_tax_residual
            gap mainTerm boundaryTerm d m) →
      (∀ m,
          conclusion_boundary_content_renormalization_necessary_tax_residual
              gap mainTerm boundaryTerm d m ≤
            ((conclusion_boundary_content_renormalization_necessary_tax_scale d m)⁻¹ /
                ((α1 : ℝ) + 1)) *
              dist m) →
        ∀ᶠ m in atTop,
          c * ((α1 : ℝ) + 1) *
              conclusion_boundary_content_renormalization_necessary_tax_scale d m ≤
            dist m

/-- Paper label: `cor:conclusion-boundary-content-renormalization-necessary-tax`. -/
theorem paper_conclusion_boundary_content_renormalization_necessary_tax :
    conclusion_boundary_content_renormalization_necessary_tax_statement := by
  intro d α1 mainTerm boundaryTerm c hc gap dist hLower hUpper
  filter_upwards [hLower] with m hm
  have hscale_pos :
      0 <
        conclusion_boundary_content_renormalization_necessary_tax_scale d m := by
    dsimp [conclusion_boundary_content_renormalization_necessary_tax_scale]
    positivity
  have halpha_pos : 0 < (α1 : ℝ) + 1 := by positivity
  have hbound := hUpper m
  have hmul :
      c * ((α1 : ℝ) + 1) *
          conclusion_boundary_content_renormalization_necessary_tax_scale d m ≤
        dist m := by
    let factor : ℝ :=
      (conclusion_boundary_content_renormalization_necessary_tax_scale d m)⁻¹ /
        ((α1 : ℝ) + 1)
    have :
        c ≤ factor * dist m := by
      simpa [factor] using le_trans hm hbound
    have hfactor_pos :
        0 < factor := by
      dsimp [factor]
      positivity
    have hscaled : c / factor ≤ dist m := by
      rw [div_le_iff₀ hfactor_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hfactor_eval :
        c / factor =
          c * ((α1 : ℝ) + 1) *
            conclusion_boundary_content_renormalization_necessary_tax_scale d m := by
      dsimp [factor]
      field_simp [hscale_pos.ne', halpha_pos.ne']
    simpa [hfactor_eval] using hscaled
  exact hmul

end Omega.Conclusion
