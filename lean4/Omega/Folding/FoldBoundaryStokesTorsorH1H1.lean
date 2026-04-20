import Mathlib.Tactic
import Omega.Folding.BoundaryHodgeStokesOrthogonalDecomposition

namespace Omega.Folding

noncomputable section

/-- Coordinate package for vector-valued boundary Stokes data. -/
structure FoldBoundaryStokesTorsorData (n : ℕ) where
  coordinateData : Fin n → BoundaryHodgeStokesData

/-- Coordinatewise vector-valued Stokes flows. -/
abbrev FoldBoundaryStokesFlow {n : ℕ} (D : FoldBoundaryStokesTorsorData n) :=
  (i : Fin n) → BoundaryHodgeStokesAmbient (D.coordinateData i).n

/-- Coordinatewise `H_1`-translation group. -/
abbrev FoldBoundaryStokesH1 {n : ℕ} (D : FoldBoundaryStokesTorsorData n) :=
  (i : Fin n) → (D.coordinateData i).cycleSpace

/-- In this one-dimensional boundary setting the `H^1` model is identified with the same
coordinatewise translation data. -/
abbrev FoldBoundaryStokesH1Cohomology {n : ℕ} (D : FoldBoundaryStokesTorsorData n) :=
  FoldBoundaryStokesH1 D

/-- The coordinatewise solution set for the vector-valued boundary Stokes problem. -/
def FoldBoundaryStokesTorsorData.solutionSet {n : ℕ} (D : FoldBoundaryStokesTorsorData n) :
    Set (FoldBoundaryStokesFlow D) :=
  {F | ∀ i, (D.coordinateData i).Feasible (F i)}

/-- The solution set is an affine torsor under the coordinatewise `H_1`-translation group. -/
def FoldBoundaryStokesTorsorData.solutionSetIsTorsorByH1 {n : ℕ}
    (D : FoldBoundaryStokesTorsorData n) : Prop :=
  ∃ F₀ : FoldBoundaryStokesFlow D,
    D.solutionSet F₀ ∧
      ∀ F, D.solutionSet F →
        ∃! h : FoldBoundaryStokesH1 D, F = fun i => F₀ i + h i

/-- The cohomological formulation uses the same coordinatewise translation model. -/
def FoldBoundaryStokesTorsorData.solutionSetIsTorsorByH1Cohomology {n : ℕ}
    (D : FoldBoundaryStokesTorsorData n) : Prop :=
  ∃ F₀ : FoldBoundaryStokesFlow D,
    D.solutionSet F₀ ∧
      ∀ F, D.solutionSet F →
        ∃! h : FoldBoundaryStokesH1Cohomology D, F = fun i => F₀ i + h i

/-- The vector-valued boundary Stokes solution set is a coordinatewise affine torsor, hence both
an `H_1`-torsor and an `H^1`-torsor. -/
theorem paper_fold_boundary_stokes_torsor_h1_h1 (n : ℕ) (D : FoldBoundaryStokesTorsorData n) :
    D.solutionSet.Nonempty → D.solutionSetIsTorsorByH1 ∧ D.solutionSetIsTorsorByH1Cohomology := by
  intro _
  classical
  let F₀ : FoldBoundaryStokesFlow D := fun i => (D.coordinateData i).orthogonalVector
  have hF₀ : D.solutionSet F₀ := by
    intro i
    exact (paper_fold_boundary_hodge_stokes_orthogonal_vector (D.coordinateData i)).1
  have htorsor :
      ∀ F, D.solutionSet F →
        ∃! h : FoldBoundaryStokesH1 D, F = fun i => F₀ i + h i := by
    intro F hF
    let h : FoldBoundaryStokesH1 D := fun i =>
      Classical.choose
        ((paper_fold_boundary_hodge_stokes_orthogonal_vector (D.coordinateData i)).2.2.1
          (F i) (hF i))
    have hh : F = fun i => F₀ i + h i := by
      funext i
      exact (Classical.choose_spec
        ((paper_fold_boundary_hodge_stokes_orthogonal_vector (D.coordinateData i)).2.2.1
          (F i) (hF i))).1
    refine ⟨h, hh, ?_⟩
    intro h' hh'
    funext i
    apply Subtype.ext
    have hi :
        F i = (D.coordinateData i).orthogonalVector + h' i := by
      simpa [F₀] using congrArg (fun G => G i) hh'
    have hSubtype :
        h' i = h i :=
      (Classical.choose_spec
        ((paper_fold_boundary_hodge_stokes_orthogonal_vector (D.coordinateData i)).2.2.1
          (F i) (hF i))).2 (h' i) hi
    exact congrArg
      (fun x : (D.coordinateData i).cycleSpace =>
        (x : BoundaryHodgeStokesAmbient (D.coordinateData i).n)) hSubtype
  refine ⟨?_, ?_⟩
  · exact ⟨F₀, hF₀, htorsor⟩
  · exact ⟨F₀, hF₀, htorsor⟩

end

end Omega.Folding
