import Mathlib.Analysis.SpecialFunctions.Sigmoid

namespace Omega.Conclusion

/-- The transport parameter used in the logistic surface-term model. -/
def conclusion_surface_term_logistic_transport_f (t : ℝ) : ℝ := t

/-- The exponential transport weight. -/
noncomputable def conclusion_surface_term_logistic_transport_q (t : ℝ) : ℝ :=
  Real.exp (-conclusion_surface_term_logistic_transport_f t)

/-- The transported surface fraction. -/
noncomputable def conclusion_surface_term_logistic_transport_sigma (t : ℝ) : ℝ :=
  Real.sigmoid (-conclusion_surface_term_logistic_transport_f t)

/-- The logarithmic surface term. -/
noncomputable def conclusion_surface_term_logistic_transport_g (t : ℝ) : ℝ :=
  -Real.log (1 + conclusion_surface_term_logistic_transport_q t)

/-- Logistic transport in the `f`-coordinate. -/
def conclusion_surface_term_logistic_transport_logistic_transport : Prop :=
  ∀ t : ℝ,
    HasDerivAt conclusion_surface_term_logistic_transport_sigma
      (-conclusion_surface_term_logistic_transport_sigma t *
        (1 - conclusion_surface_term_logistic_transport_sigma t)) t

/-- The explicit closed forms for the surface transport profile and surface term. -/
def conclusion_surface_term_logistic_transport_explicit_closed_form : Prop :=
  conclusion_surface_term_logistic_transport_sigma 0 = (1 / 2 : ℝ) ∧
    ∀ t : ℝ,
      conclusion_surface_term_logistic_transport_sigma t =
          1 / (1 + Real.exp (conclusion_surface_term_logistic_transport_f t)) ∧
        conclusion_surface_term_logistic_transport_g t =
          -Real.log (1 + Real.exp (-conclusion_surface_term_logistic_transport_f t))

private lemma conclusion_surface_term_logistic_transport_sigma_hasDerivAt (t : ℝ) :
    HasDerivAt conclusion_surface_term_logistic_transport_sigma
      (-conclusion_surface_term_logistic_transport_sigma t *
        (1 - conclusion_surface_term_logistic_transport_sigma t)) t := by
  simpa [conclusion_surface_term_logistic_transport_sigma,
    conclusion_surface_term_logistic_transport_f]
    using ((Real.hasDerivAt_sigmoid (-t)).comp t (hasDerivAt_neg t))

private lemma conclusion_surface_term_logistic_transport_sigma_closed_form (t : ℝ) :
    conclusion_surface_term_logistic_transport_sigma t =
      1 / (1 + Real.exp (conclusion_surface_term_logistic_transport_f t)) := by
  simp [conclusion_surface_term_logistic_transport_sigma,
    conclusion_surface_term_logistic_transport_f, Real.sigmoid_def, one_div]

/-- Paper label: `thm:conclusion-surface-term-logistic-transport`. -/
theorem paper_conclusion_surface_term_logistic_transport :
    conclusion_surface_term_logistic_transport_logistic_transport ∧
      conclusion_surface_term_logistic_transport_explicit_closed_form := by
  refine ⟨?_, ?_⟩
  · intro t
    exact conclusion_surface_term_logistic_transport_sigma_hasDerivAt t
  · refine ⟨?_, ?_⟩
    · norm_num [conclusion_surface_term_logistic_transport_sigma,
        conclusion_surface_term_logistic_transport_f, Real.sigmoid_def]
    · intro t
      refine ⟨conclusion_surface_term_logistic_transport_sigma_closed_form t, ?_⟩
      simp [conclusion_surface_term_logistic_transport_g,
        conclusion_surface_term_logistic_transport_q,
        conclusion_surface_term_logistic_transport_f]

end Omega.Conclusion
