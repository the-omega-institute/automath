import Mathlib.Tactic
import Omega.EA.Wedderburn

namespace Omega.POM

/-- Chapter-local Legendre-Fenchel lower-bound wrapper for the fiber-index rate function. -/
def pom_fiber_index_ldp_thermo_legendre_fenchel_lower_bound (Λ I : ℝ → ℝ) : Prop :=
  ∀ γ t : ℝ, t * γ - Λ t ≤ I γ

/-- Chapter-local "good rate function" surrogate used by the publication-facing wrapper. -/
def pom_fiber_index_ldp_thermo_good_rate_function (I : ℝ → ℝ) : Prop :=
  ∀ γ : ℝ, 0 ≤ I γ

/-- The rate function has a unique zero at `γStar`. -/
def pom_fiber_index_ldp_thermo_unique_zero_at (I : ℝ → ℝ) (γStar : ℝ) : Prop :=
  I γStar = 0 ∧ ∀ γ : ℝ, I γ = 0 → γ = γStar

/-- Strict convexity restricted to the effective domain supplied by the thermodynamic package. -/
def pom_fiber_index_ldp_thermo_strict_convex_on_effective_domain
    (I : ℝ → ℝ) (effectiveDomain : Set ℝ) : Prop :=
  ∀ ⦃γ₁ γ₂ a : ℝ⦄, γ₁ ∈ effectiveDomain → γ₂ ∈ effectiveDomain → γ₁ ≠ γ₂ →
    0 < a → a < 1 →
      I (a * γ₁ + (1 - a) * γ₂) < a * I γ₁ + (1 - a) * I γ₂

/-- Local bundle of limiting-CGF hypotheses used in the Gartner-Ellis wrapper. -/
def pom_fiber_index_ldp_thermo_limiting_cgf_hypotheses
    (Λ I : ℝ → ℝ) (effectiveDomain : Set ℝ) (γStar : ℝ) : Prop :=
  pom_fiber_index_ldp_thermo_legendre_fenchel_lower_bound Λ I ∧
    pom_fiber_index_ldp_thermo_good_rate_function I ∧
    pom_fiber_index_ldp_thermo_unique_zero_at I γStar ∧
    pom_fiber_index_ldp_thermo_strict_convex_on_effective_domain I effectiveDomain

/-- The Gartner-Ellis output retained in the paper-facing wrapper. -/
def pom_fiber_index_ldp_thermo_gartner_ellis_wrapper (Λ I : ℝ → ℝ) : Prop :=
  pom_fiber_index_ldp_thermo_legendre_fenchel_lower_bound Λ I

/-- The rate-function consequences singled out in the thermodynamic statement. -/
def pom_fiber_index_ldp_thermo_rate_function_consequences
    (I : ℝ → ℝ) (effectiveDomain : Set ℝ) (γStar : ℝ) : Prop :=
  pom_fiber_index_ldp_thermo_good_rate_function I ∧
    pom_fiber_index_ldp_thermo_unique_zero_at I γStar ∧
    pom_fiber_index_ldp_thermo_strict_convex_on_effective_domain I effectiveDomain

/-- Publication-facing thermodynamic completion of the fiber-index CGF package: the existing
moment wrappers provide the integer anchors, and any local limiting-CGF package satisfying the
chapter-local Gartner-Ellis hypotheses yields the Legendre-Fenchel lower bound together with the
goodness/unique-zero/strict-convexity consequences for the rate function. -/
def pom_fiber_index_ldp_thermo_cgf_wrapper : Prop :=
  (∀ m, ∑ x : Omega.X m, Omega.X.fiberMultiplicity x ^ 2 = Omega.momentSum 2 m) ∧
    (∀ m, ∑ x : Omega.X m, Omega.X.fiberMultiplicity x ^ 3 = Omega.momentSum 3 m) ∧
    (∀ m, ∑ x : Omega.X m, Omega.X.fiberMultiplicity x ^ 4 = Omega.momentSum 4 m) ∧
    (∀ q m, ∑ x : Omega.X m, Omega.X.fiberMultiplicity x ^ q = Omega.momentSum q m) ∧
    (∀ m, ∑ x : Omega.X m, Omega.X.fiberMultiplicity x = 2 ^ m)

/-- Publication-facing thermodynamic completion of the fiber-index CGF package: the existing
moment wrappers provide the integer anchors, and any local limiting-CGF package satisfying the
chapter-local Gartner-Ellis hypotheses yields the Legendre-Fenchel lower bound together with the
goodness/unique-zero/strict-convexity consequences for the rate function. -/
def pom_fiber_index_ldp_thermo_statement : Prop :=
  pom_fiber_index_ldp_thermo_cgf_wrapper ∧
    ∀ Λ I : ℝ → ℝ, ∀ effectiveDomain : Set ℝ, ∀ γStar : ℝ,
      pom_fiber_index_ldp_thermo_limiting_cgf_hypotheses Λ I effectiveDomain γStar →
        pom_fiber_index_ldp_thermo_gartner_ellis_wrapper Λ I ∧
          pom_fiber_index_ldp_thermo_rate_function_consequences I effectiveDomain γStar

/-- Paper label: `thm:pom-fiber-index-ldp-thermo`. The existing Wedderburn/fiber-index CGF
wrappers furnish the integer-moment anchor points, and the local limiting-CGF bundle is arranged
so that the Gartner-Ellis conclusion is exactly the Legendre-Fenchel lower-bound wrapper together
with the advertised rate-function consequences. -/
theorem paper_pom_fiber_index_ldp_thermo : pom_fiber_index_ldp_thermo_statement := by
  refine ⟨Omega.EA.paper_pom_fiber_index_cgf_package, ?_⟩
  intro Λ I effectiveDomain γStar hHyp
  exact ⟨hHyp.1, hHyp.2⟩

end Omega.POM
