import Omega.Zeta.XiTimeOnlyConservedQuantity

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-initial-generator-for-resources`. Applying the time-only
classification to the corrected resource `R - gamma` leaves a scalar multiple of elapsed length
and then restores the gauge term. -/
theorem paper_xi_time_initial_generator_for_resources
    (C : xi_time_only_conserved_quantity_system) (R gamma : C.Mor -> ℝ)
    (hbasic : ∀ e, C.BasicReversible e -> R e - gamma e = 0)
    (hadd : ∀ {u v}, C.Composable u v ->
      R (C.comp u v) - gamma (C.comp u v) = (R u - gamma u) + (R v - gamma v)) :
    ∃ c : ℝ, ∀ w, R w = c * C.length w + gamma w := by
  let I : C.Mor → ℝ := fun w => R w - gamma w
  obtain ⟨c, hc⟩ :=
    paper_xi_time_only_conserved_quantity C I
      (by
        intro e he
        exact hbasic e he)
      (by
        intro u v huv
        exact hadd huv)
  refine ⟨c, ?_⟩
  intro w
  have hw : R w - gamma w = c * C.length w := hc w
  linarith

end Omega.Zeta
