import Mathlib.Tactic

namespace Omega.Conclusion

/-- Polynomial finite-resolution cost `N(σ) = 2 / σ^2` for the scale-kernel tail model. -/
noncomputable def conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_resolution_cost
    (σ : ℝ) : ℝ :=
  2 / σ ^ 2

/-- The squared Wasserstein tail envelope `2 / N`. -/
noncomputable def conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_tail_variance
    (N : ℝ) : ℝ :=
  2 / N

/-- Fixed-band multiplier bound, independent of the tail cutoff. -/
noncomputable def conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_band_bound
    (Ω : ℝ) : ℝ :=
  Real.exp ((Real.pi ^ 2 / 6) * Ω ^ 2)

/-- Limiting multiplier growth forced by resolving scale `σ`. -/
noncomputable def conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_exact_cost
    (σ : ℝ) : ℝ :=
  Real.exp (Real.pi / σ)

/-- Paper label: `thm:conclusion-scalekernel-fourth-order-visible-but-costly-to-remove`.

The finite-resolution branch uses the tail variance identity at `N(σ) = 2 / σ^2`; the fixed-band
branch records the uniform multiplier bound, while exact removal carries the exponential
`exp(π / σ)` cost. -/
theorem paper_conclusion_scalekernel_fourth_order_visible_but_costly_to_remove
    (σ Ω W2 fixedBandAmplification limitingAmplification : ℝ) (hσ : 0 < σ)
    (hW2tail :
      W2 ^ 2 ≤
        conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_tail_variance
          (conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_resolution_cost σ))
    (hFixed :
      fixedBandAmplification ≤
        conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_band_bound Ω)
    (hLimit :
      limitingAmplification =
        conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_exact_cost σ) :
    conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_tail_variance
        (conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_resolution_cost σ) =
        σ ^ 2 ∧
      W2 ≤ σ ∧
      fixedBandAmplification ≤
        conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_band_bound Ω ∧
      limitingAmplification = Real.exp (Real.pi / σ) := by
  have htail :
      conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_tail_variance
        (conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_resolution_cost σ) =
        σ ^ 2 := by
    unfold conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_tail_variance
      conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_resolution_cost
    field_simp [hσ.ne']
  have hW2sq : W2 ^ 2 ≤ σ ^ 2 := by
    simpa [htail] using hW2tail
  have hW2le : W2 ≤ σ := by
    nlinarith [sq_nonneg (W2 - σ)]
  refine ⟨htail, hW2le, hFixed, ?_⟩
  simpa [conclusion_scalekernel_fourth_order_visible_but_costly_to_remove_exact_cost] using hLimit

end Omega.Conclusion
