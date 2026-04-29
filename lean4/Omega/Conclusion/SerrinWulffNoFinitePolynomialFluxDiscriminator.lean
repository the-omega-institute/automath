import Mathlib.Tactic
import Omega.Conclusion.SerrinWulffFiniteOrderBoundaryMomentCamouflage

namespace Omega.Conclusion

open scoped BigOperators

/-- The concrete Wulff-side finite moment witness used in the discriminator obstruction. -/
def conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy :
    Finset ℕ :=
  conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive

/-- The matching non-Wulff finite moment witness used in the discriminator obstruction. -/
def conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy :
    Finset ℕ :=
  conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative

/-- The moment functional used by the no-discriminator abstraction. -/
def conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moment
    (S : Finset ℕ) (k : ℕ) : ℤ :=
  conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment S k

/-- A finite flux family factors through moments up to degree `r`. -/
def conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_factors_through_moments
    {N : ℕ} (r : ℕ) (flux : Fin N → Finset ℕ → ℤ) : Prop :=
  ∀ j A B,
    (∀ k, k ≤ r →
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moment A k =
        conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moment B k) →
    flux j A = flux j B

/-- An iff discriminator for the singleton Wulff proxy by a finite flux vector. -/
def conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_iff_wulff_proxy
    {N : ℕ} (flux : Fin N → Finset ℕ → ℤ) : Prop :=
  ∀ Ω : Finset ℕ,
    Ω = conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy ↔
      ∀ j : Fin N,
        flux j Ω =
          flux j conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy

/-- Concrete no-discriminator statement for finite polynomial flux families. -/
def conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_statement : Prop :=
  ∀ (N : ℕ) (flux : Fin N → Finset ℕ → ℤ),
    conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_factors_through_moments
        1 flux →
      ¬ conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_iff_wulff_proxy flux

/-- The two concrete proxies have identical moments through degree one. -/
lemma conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moments_match_order_one :
    ∀ k, k ≤ 1 →
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moment
          conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy k =
        conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moment
          conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy k := by
  intro k hk
  interval_cases k
  · norm_num [conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moment,
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy,
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class]
  · norm_num [conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moment,
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy,
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_moment,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class]

/-- The camouflage proxy is not the Wulff proxy. -/
lemma conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_ne_wulff :
    conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy ≠
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy := by
  intro hEq
  have hmem :
      7 ∈ conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy := by
    simp [conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_negative,
      conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
      Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class]
  have :
      7 ∈ conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy := by
    simpa [hEq] using hmem
  simp [conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy,
    conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_positive,
    conclusion_serrin_wulff_finite_order_boundary_moment_camouflage_affine,
    Omega.SPG.spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class] at this

/-- Paper label:
`cor:conclusion-serrin-wulff-no-finite-polynomial-flux-discriminator`. -/
theorem paper_conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator :
    conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_statement := by
  intro N flux hfactor hdisc
  have hsame :
      ∀ j : Fin N,
        flux j conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy =
          flux j conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy := by
    intro j
    exact hfactor j
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_moments_match_order_one
  have hEq :
      conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy =
        conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_wulff_proxy :=
    (hdisc conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_proxy).2
      hsame
  exact conclusion_serrin_wulff_no_finite_polynomial_flux_discriminator_camouflage_ne_wulff hEq

end Omega.Conclusion
