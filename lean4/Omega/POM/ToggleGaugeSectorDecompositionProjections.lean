import Mathlib
import Mathlib.Tactic
import Omega.POM.ToggleGaugeInvariantEndomorphismsC2Tensor

namespace Omega.POM

open scoped BigOperators

/-- The subset-indexed sector projection in the tensor-basis model. -/
def pom_toggle_gauge_sector_decomposition_projections_sector_projection
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data)
    (S : Finset (Fin x.r)) : Finset (Fin x.r) → ℤ :=
  fun T => if T = S then 1 else 0

/-- A diagonal operator in the subset basis, recorded by its scalar on each sector. -/
def pom_toggle_gauge_sector_decomposition_projections_diagonal_operator
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data)
    (a : Finset (Fin x.r) → ℤ) : Finset (Fin x.r) → ℤ :=
  a

/-- Paper-facing package for the subset-indexed sector decomposition coming from the tensor-basis
equivalence: the basis is indexed by subsets of `Fin x.r`, the symbolic sector projections are
pairwise orthogonal and complete, and every diagonal operator acts by a scalar on each sector. -/
def pom_toggle_gauge_sector_decomposition_projections_statement
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) : Prop :=
  Nonempty
      (pom_toggle_gauge_invariant_endomorphisms_c2_tensor_tensor_basis x ≃ Finset (Fin x.r)) ∧
    (∀ S T : Finset (Fin x.r),
      pom_toggle_gauge_sector_decomposition_projections_sector_projection x S *
          pom_toggle_gauge_sector_decomposition_projections_sector_projection x T =
        if S = T then pom_toggle_gauge_sector_decomposition_projections_sector_projection x S
        else 0) ∧
    (∑ S : Finset (Fin x.r),
        pom_toggle_gauge_sector_decomposition_projections_sector_projection x S = 1) ∧
    ∀ a : Finset (Fin x.r) → ℤ, ∀ S : Finset (Fin x.r),
      pom_toggle_gauge_sector_decomposition_projections_diagonal_operator x a *
          pom_toggle_gauge_sector_decomposition_projections_sector_projection x S =
        a S • pom_toggle_gauge_sector_decomposition_projections_sector_projection x S

private theorem pom_toggle_gauge_sector_decomposition_projections_sector_projection_orthogonal
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) :
    ∀ S T : Finset (Fin x.r),
      pom_toggle_gauge_sector_decomposition_projections_sector_projection x S *
          pom_toggle_gauge_sector_decomposition_projections_sector_projection x T =
        if S = T then pom_toggle_gauge_sector_decomposition_projections_sector_projection x S
        else 0 := by
  intro S T
  ext U
  by_cases hST : S = T
  · subst hST
    by_cases hUS : U = S
    · simp [pom_toggle_gauge_sector_decomposition_projections_sector_projection, hUS]
    · simp [pom_toggle_gauge_sector_decomposition_projections_sector_projection, hUS]
  · by_cases hUS : U = S
    · have hUT : U ≠ T := by
        intro hUT
        apply hST
        simpa [hUS] using hUT
      simp [pom_toggle_gauge_sector_decomposition_projections_sector_projection, hST, hUS]
    · simp [pom_toggle_gauge_sector_decomposition_projections_sector_projection, hST, hUS]

private theorem pom_toggle_gauge_sector_decomposition_projections_sector_projection_complete
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) :
    ∑ S : Finset (Fin x.r),
      pom_toggle_gauge_sector_decomposition_projections_sector_projection x S = 1 := by
  ext U
  simp [pom_toggle_gauge_sector_decomposition_projections_sector_projection]

private theorem pom_toggle_gauge_sector_decomposition_projections_diagonalizes
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data)
    (a : Finset (Fin x.r) → ℤ) (S : Finset (Fin x.r)) :
    pom_toggle_gauge_sector_decomposition_projections_diagonal_operator x a *
        pom_toggle_gauge_sector_decomposition_projections_sector_projection x S =
      a S • pom_toggle_gauge_sector_decomposition_projections_sector_projection x S := by
  ext T
  by_cases hTS : T = S
  · subst hTS
    simp [pom_toggle_gauge_sector_decomposition_projections_diagonal_operator,
      pom_toggle_gauge_sector_decomposition_projections_sector_projection]
  · simp [pom_toggle_gauge_sector_decomposition_projections_diagonal_operator,
      pom_toggle_gauge_sector_decomposition_projections_sector_projection, hTS]

/-- Paper label: `cor:pom-toggle-gauge-sector-decomposition-projections`. -/
theorem paper_pom_toggle_gauge_sector_decomposition_projections
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) :
    pom_toggle_gauge_sector_decomposition_projections_statement x := by
  rcases paper_pom_toggle_gauge_invariant_endomorphisms_c2_tensor x with ⟨-, -, hEquiv⟩
  refine ⟨hEquiv,
    pom_toggle_gauge_sector_decomposition_projections_sector_projection_orthogonal x,
    pom_toggle_gauge_sector_decomposition_projections_sector_projection_complete x, ?_⟩
  intro a S
  exact pom_toggle_gauge_sector_decomposition_projections_diagonalizes x a S

end Omega.POM
