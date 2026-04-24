import Mathlib.Tactic
import Omega.Conclusion.BoundaryGodelVsIsotropicMomentExponentialIncompressibility

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-subcritical-isotropic-moment-certificates-incomplete-across-resolutions`. If a
subcritical sketch size `rₘ` were still complete after postprocessing, the composite isotropic
moment certificate would be injective, contradicting the previously established lower bound
`2^(mn) ≤ rₘ`. -/
theorem paper_conclusion_subcritical_isotropic_moment_certificates_incomplete_across_resolutions
    (m n r_m : ℕ) (hr_m : r_m < 2 ^ (m * n))
    {Y_m : Type*} (momentMap : Fin (2 ^ (m * n)) → Fin r_m)
    (postSketch : Fin r_m → Y_m) :
    ∃ u v : Fin (2 ^ (m * n)), u ≠ v ∧ postSketch (momentMap u) = postSketch (momentMap v) := by
  by_contra hNoPair
  have hInjective : Function.Injective (fun u => postSketch (momentMap u)) := by
    intro u v huv
    by_contra hne
    exact hNoPair ⟨u, v, hne, huv⟩
  have hlower :
      2 ^ (m * n) ≤ r_m :=
    (paper_conclusion_boundary_godel_vs_isotropic_moment_exponential_incompressibility
      m n r_m momentMap postSketch hInjective).2.2
  exact (not_le_of_gt hr_m) hlower

end Omega.Conclusion
