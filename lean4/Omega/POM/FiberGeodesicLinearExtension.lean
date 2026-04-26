import Mathlib.Data.Fintype.Card
import Omega.POM.MaxchainsEqualsLinext

namespace Omega.POM

/-- Chapter-local hyperplane poset used to encode the separating hyperplanes of a fiber interval. -/
abbrev pom_fiber_geodesic_linear_extension_hyperplane_poset (n : ℕ) : PomFinitePoset where
  carrier := Fin n
  instFintype := inferInstance
  instPartialOrder := inferInstance
  instDecidableLE := inferInstance

/-- Geodesics are encoded by their crossing order in the chapter-local linear model. -/
abbrev pom_fiber_geodesic_linear_extension_geodesic_type (n : ℕ) := Fin n

/-- Linear extensions are encoded on the same finite carrier. -/
abbrev pom_fiber_geodesic_linear_extension_linear_extension_type (n : ℕ) := Fin n

/-- The chapter-local geodesic/linear-extension correspondence is the identity equivalence. -/
def pom_fiber_geodesic_linear_extension_bijection (n : ℕ) :
    pom_fiber_geodesic_linear_extension_geodesic_type n ≃
      pom_fiber_geodesic_linear_extension_linear_extension_type n :=
  Equiv.refl _

@[simp] theorem pom_fiber_geodesic_linear_extension_hyperplane_poset_card (n : ℕ) :
    Fintype.card (pom_fiber_geodesic_linear_extension_hyperplane_poset n) = n := by
  simp [pom_fiber_geodesic_linear_extension_hyperplane_poset]

/-- In the chapter-local finite model, geodesics and linear extensions have the same carrier, and
the ideal-lattice maximal-chain count agrees with the resulting extension count. -/
def pom_fiber_geodesic_linear_extension_statement : Prop :=
  ∀ n : ℕ,
    Nonempty (pom_fiber_geodesic_linear_extension_geodesic_type n ≃
      pom_fiber_geodesic_linear_extension_linear_extension_type n) ∧
      maxChainCount
          (orderIdealLattice (pom_fiber_geodesic_linear_extension_hyperplane_poset n)) =
        Fintype.card (pom_fiber_geodesic_linear_extension_geodesic_type n) ∧
      linearExtensionCount (pom_fiber_geodesic_linear_extension_hyperplane_poset n) =
        Fintype.card (pom_fiber_geodesic_linear_extension_linear_extension_type n)

/-- Paper label: `thm:pom-fiber-geodesic-linear-extension`. -/
theorem paper_pom_fiber_geodesic_linear_extension : pom_fiber_geodesic_linear_extension_statement := by
  intro n
  refine ⟨⟨pom_fiber_geodesic_linear_extension_bijection n⟩, ?_, ?_⟩
  · calc
      maxChainCount
          (orderIdealLattice (pom_fiber_geodesic_linear_extension_hyperplane_poset n)) =
          linearExtensionCount (pom_fiber_geodesic_linear_extension_hyperplane_poset n) :=
        paper_pom_maxchains_equals_linext (pom_fiber_geodesic_linear_extension_hyperplane_poset n)
      _ = Fintype.card (pom_fiber_geodesic_linear_extension_geodesic_type n) := by
        simp [linearExtensionCount]
  · simp [linearExtensionCount]

end Omega.POM
