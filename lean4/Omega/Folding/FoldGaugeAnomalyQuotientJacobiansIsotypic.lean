import Omega.CircleDimension.S4A4QuotientIsLeyangCurve
import Omega.CircleDimension.S4V4JacobianPullbackKernelPrymSplitting

namespace Omega.Folding

/-- Paper label: `cor:fold-gauge-anomaly-quotient-jacobians-isotypic`.
The `A₄`-invariant quotient is the Lee--Yang curve, while the `V₄`-invariant packet is the
chapter-local Jacobian/Prym splitting with its `A₂`-polarized Prym factor. -/
theorem paper_fold_gauge_anomaly_quotient_jacobians_isotypic (P : Polynomial ℚ) :
    Nonempty
      (Omega.CircleDimension.cdim_s4_a4_quotient_is_leyang_curve_a4_quotient_point P ≃
        Omega.CircleDimension.cdim_s4_a4_quotient_is_leyang_curve_leyang_point P) ∧
      Omega.CircleDimension.s4v4CompatibleBiellipticPencils.card = 3 ∧
      (let D :=
          Omega.CircleDimension.cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data
       D.standardGeneratorExists ∧ D.invariantPolarizationsAreA2 ∧
        D.naturalPrymPolarizationIsA2) ∧
      Omega.CircleDimension.a2CartanForm.det = 3 := by
  refine ⟨Omega.CircleDimension.paper_cdim_s4_a4_quotient_is_leyang_curve P, ?_⟩
  rcases Omega.CircleDimension.paper_cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting with
    ⟨hpencils, hprym, hdet, _, _⟩
  exact ⟨hpencils, hprym, hdet⟩

end Omega.Folding
