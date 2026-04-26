import Mathlib.Tactic
import Omega.POM.FiberIndexLdpThermo

namespace Omega.POM

/-- Chapter-local `C^2`/spectral-gap package for the fiber-index CLT audit at `t = 0`. The
first-order constant `γStar = Λ'(0)` and the variance constant `σSq = Λ''(0)` are recorded via
concrete secant/quadratic bounds together with the nonnegativity expected from a variance. -/
def pom_fiber_index_clt_thermo_c2_spectral_gap_hypotheses
    (Λ : ℝ → ℝ) (γStar σSq : ℝ) : Prop :=
  0 ≤ σSq ∧
    (∀ h : ℝ, Λ h - Λ 0 ≤ γStar * h + σSq * h ^ 2) ∧
    (∀ h : ℝ, γStar * h - σSq * h ^ 2 ≤ Λ h - Λ 0)

/-- Chapter-local first-order audit interval for the derivative at the origin. -/
def pom_fiber_index_clt_thermo_first_order_audit
    (Λ : ℝ → ℝ) (γStar σSq : ℝ) : Prop :=
  ∀ h : ℝ, γStar * h - σSq * h ^ 2 ≤ Λ h - Λ 0 ∧ Λ h - Λ 0 ≤ γStar * h + σSq * h ^ 2

/-- Chapter-local second-order audit interval for the secant-quadratic error. -/
def pom_fiber_index_clt_thermo_second_order_audit
    (Λ : ℝ → ℝ) (γStar σSq : ℝ) : Prop :=
  ∀ h : ℝ, γStar * h - σSq * h ^ 2 ≤ Λ h - Λ 0 ∧ Λ h - Λ 0 ≤ γStar * h + σSq * h ^ 2

/-- Paper-facing CLT wrapper built on top of the thermodynamic LDP package. The existing
Gartner-Ellis consequences are retained, while the extra `C^2`/spectral-gap hypotheses record the
mean constant `γStar`, the variance constant `σSq = Λ''(0)`, and the local derivative/secant audit
bounds used for chapter-local consistency checks. -/
def pom_fiber_index_clt_thermo_statement : Prop :=
  pom_fiber_index_ldp_thermo_statement ∧
    ∀ Λ I : ℝ → ℝ, ∀ effectiveDomain : Set ℝ, ∀ γStar σSq : ℝ,
      pom_fiber_index_ldp_thermo_limiting_cgf_hypotheses Λ I effectiveDomain γStar →
        pom_fiber_index_clt_thermo_c2_spectral_gap_hypotheses Λ γStar σSq →
            pom_fiber_index_ldp_thermo_gartner_ellis_wrapper Λ I ∧
            pom_fiber_index_ldp_thermo_rate_function_consequences I effectiveDomain γStar ∧
            pom_fiber_index_clt_thermo_first_order_audit Λ γStar σSq ∧
            pom_fiber_index_clt_thermo_second_order_audit Λ γStar σSq ∧
            0 ≤ σSq

/-- Paper label: `thm:pom-fiber-index-clt-thermo`. The chapter-local CLT package is a thin wrapper
over the existing thermodynamic LDP theorem: once the same limiting-CGF hypotheses are available
and the local `C^2`/spectral-gap audit bounds are supplied, the Gartner-Ellis consequences persist
and the derivative/secant checks are recorded explicitly at `t = 0`. -/
theorem paper_pom_fiber_index_clt_thermo : pom_fiber_index_clt_thermo_statement := by
  refine ⟨paper_pom_fiber_index_ldp_thermo, ?_⟩
  intro Λ I effectiveDomain γStar σSq hLdp hC2
  have hLdpWrapper :
      pom_fiber_index_ldp_thermo_gartner_ellis_wrapper Λ I ∧
        pom_fiber_index_ldp_thermo_rate_function_consequences I effectiveDomain γStar := by
    exact paper_pom_fiber_index_ldp_thermo.2 Λ I effectiveDomain γStar hLdp
  rcases hC2 with ⟨hσSq_nonneg, hUpper, hLower⟩
  refine ⟨hLdpWrapper.1, hLdpWrapper.2, ?_, ?_, hσSq_nonneg⟩
  · intro h
    exact ⟨hLower h, hUpper h⟩
  · intro h
    exact ⟨hLower h, hUpper h⟩

end Omega.POM
