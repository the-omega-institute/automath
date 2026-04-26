import Mathlib

namespace Omega.POM

/-- Concrete anomaly routes, recorded as the list of rewrite labels accumulated along the route. -/
abbrev pom_anom_additive_up_to_boundary_route := List ℤ

/-- Total anomaly accumulated along a route. -/
def pom_anom_additive_up_to_boundary_accumulatedSum
    (route : pom_anom_additive_up_to_boundary_route) : ℤ :=
  route.sum

/-- Vertical composition of composable rewrite routes. -/
def pom_anom_additive_up_to_boundary_verticalCompose
    (left right : pom_anom_additive_up_to_boundary_route) :
    pom_anom_additive_up_to_boundary_route :=
  left ++ right

/-- The boundary cochain comparing two normalization routes is the difference of their accumulated
anomaly labels. -/
def pom_anom_additive_up_to_boundary_boundaryCochain
    (left right : pom_anom_additive_up_to_boundary_route) : ℤ :=
  pom_anom_additive_up_to_boundary_accumulatedSum left -
    pom_anom_additive_up_to_boundary_accumulatedSum right

/-- Normalized anomaly after subtracting the chosen boundary correction. -/
def pom_anom_additive_up_to_boundary_normalizedAnomaly
    (route : pom_anom_additive_up_to_boundary_route) (boundary : ℤ) : ℤ :=
  pom_anom_additive_up_to_boundary_accumulatedSum route - boundary

/-- Additivity under vertical composition and boundary invariance of the normalized anomaly. -/
def pom_anom_additive_up_to_boundary_statement : Prop :=
  (∀ left right : pom_anom_additive_up_to_boundary_route,
      pom_anom_additive_up_to_boundary_accumulatedSum
          (pom_anom_additive_up_to_boundary_verticalCompose left right) =
        pom_anom_additive_up_to_boundary_accumulatedSum left +
          pom_anom_additive_up_to_boundary_accumulatedSum right) ∧
    ∀ left right : pom_anom_additive_up_to_boundary_route,
      pom_anom_additive_up_to_boundary_normalizedAnomaly left
          (pom_anom_additive_up_to_boundary_boundaryCochain left right) =
        pom_anom_additive_up_to_boundary_normalizedAnomaly right 0

/-- Paper label: `prop:pom-anom-additive-up-to-boundary`. -/
theorem paper_pom_anom_additive_up_to_boundary : pom_anom_additive_up_to_boundary_statement := by
  refine ⟨?_, ?_⟩
  · intro left right
    simp [pom_anom_additive_up_to_boundary_accumulatedSum,
      pom_anom_additive_up_to_boundary_verticalCompose, List.sum_append]
  · intro left right
    unfold pom_anom_additive_up_to_boundary_normalizedAnomaly
      pom_anom_additive_up_to_boundary_boundaryCochain
      pom_anom_additive_up_to_boundary_accumulatedSum
    ring

end Omega.POM
