import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace Omega.Folding

noncomputable section

abbrev BoundaryHodgeStokesAmbient (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

/-- Concrete data for the affine boundary Hodge--Stokes problem. The boundary datum is written as
an orthogonal component plus a cycle-space correction, and the orthogonal component is assumed to
be orthogonal to every cycle. -/
structure BoundaryHodgeStokesData where
  n : ℕ
  boundaryVector : BoundaryHodgeStokesAmbient n
  cycleSpace : Submodule ℝ (BoundaryHodgeStokesAmbient n)
  orthogonalVector : BoundaryHodgeStokesAmbient n
  cycleOffset : cycleSpace
  boundary_split : boundaryVector = orthogonalVector + cycleOffset
  orthogonalToCycles :
    ∀ h : BoundaryHodgeStokesAmbient n, h ∈ cycleSpace →
      @inner ℝ (BoundaryHodgeStokesAmbient n) _ orthogonalVector h = 0

/-- Feasible flows are the affine translate of the cycle space through the boundary datum. -/
def BoundaryHodgeStokesData.Feasible (D : BoundaryHodgeStokesData)
    (g : BoundaryHodgeStokesAmbient D.n) : Prop :=
  ∃ h ∈ D.cycleSpace, g = D.boundaryVector + h

/-- Package for the vector-valued Hodge--Stokes minimum-energy representative. -/
def BoundaryHodgeStokesOrthogonalVectorPackage (D : BoundaryHodgeStokesData) : Prop :=
  D.Feasible D.orthogonalVector ∧
    (∀ h ∈ D.cycleSpace, @inner ℝ (BoundaryHodgeStokesAmbient D.n) _ D.orthogonalVector h = 0) ∧
    (∀ g, D.Feasible g → ∃! h : D.cycleSpace, g = D.orthogonalVector + h) ∧
    (∀ g, D.Feasible g →
      ‖g‖ ^ 2 = ‖D.orthogonalVector‖ ^ 2 + ‖g - D.orthogonalVector‖ ^ 2) ∧
    (∀ g, D.Feasible g → ‖D.orthogonalVector‖ ≤ ‖g‖)

/-- Paper label: `cor:fold-boundary-hodge-stokes-orthogonal-vector`. -/
theorem paper_fold_boundary_hodge_stokes_orthogonal_vector
    (D : BoundaryHodgeStokesData) : BoundaryHodgeStokesOrthogonalVectorPackage D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨-D.cycleOffset, Submodule.neg_mem _ D.cycleOffset.property, ?_⟩
    calc
      D.orthogonalVector
          = D.orthogonalVector + D.cycleOffset + (-D.cycleOffset : BoundaryHodgeStokesAmbient D.n) := by
              simp
      _ = D.boundaryVector + (-D.cycleOffset : BoundaryHodgeStokesAmbient D.n) := by
            rw [D.boundary_split]
  · intro h hh
    exact D.orthogonalToCycles h hh
  · intro g hg
    rcases hg with ⟨k, hk, rfl⟩
    refine ⟨⟨D.cycleOffset + k, Submodule.add_mem _ D.cycleOffset.property hk⟩, ?_, ?_⟩
    · rw [D.boundary_split]
      simp [add_left_comm, add_comm]
    · intro h hh
      apply Subtype.ext
      have hh' := congrArg (fun x => x - D.orthogonalVector) hh
      have hh'' : k + (D.cycleOffset : BoundaryHodgeStokesAmbient D.n) = h := by
        rw [D.boundary_split] at hh'
        abel_nf at hh'
        simpa [add_comm] using hh'
      simpa [add_comm] using hh''.symm
  · intro g hg
    rcases hg with ⟨k, hk, rfl⟩
    have hsum_mem : (D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k ∈ D.cycleSpace :=
      Submodule.add_mem _ D.cycleOffset.property hk
    have horth :
        @inner ℝ (BoundaryHodgeStokesAmbient D.n) _ D.orthogonalVector
            ((D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k) = 0 :=
      D.orthogonalToCycles _ hsum_mem
    have hsplit :
        D.boundaryVector + k =
          D.orthogonalVector + ((D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k) := by
      rw [D.boundary_split]
      abel
    calc
      ‖D.boundaryVector + k‖ ^ 2
          = ‖D.orthogonalVector + ((D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k)‖ ^ 2 := by
              rw [hsplit]
      _ = ‖D.orthogonalVector‖ ^ 2 + ‖(D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k‖ ^ 2 := by
            simpa [pow_two, real_inner_comm, horth] using
              norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      _ = ‖D.orthogonalVector‖ ^ 2 + ‖D.boundaryVector + k - D.orthogonalVector‖ ^ 2 := by
            congr 1
            rw [D.boundary_split]
            abel
  · intro g hg
    rcases hg with ⟨k, hk, rfl⟩
    have hsum_mem : (D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k ∈ D.cycleSpace :=
      Submodule.add_mem _ D.cycleOffset.property hk
    have horth :
        @inner ℝ (BoundaryHodgeStokesAmbient D.n) _ D.orthogonalVector
            ((D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k) = 0 :=
      D.orthogonalToCycles _ hsum_mem
    have hsplit :
        D.boundaryVector + k =
          D.orthogonalVector + ((D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k) := by
      rw [D.boundary_split]
      abel
    have hpyth :
        ‖D.boundaryVector + k‖ ^ 2 =
          ‖D.orthogonalVector‖ ^ 2 + ‖D.boundaryVector + k - D.orthogonalVector‖ ^ 2 := by
      calc
        ‖D.boundaryVector + k‖ ^ 2
            = ‖D.orthogonalVector + ((D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k)‖ ^ 2 := by
                rw [hsplit]
        _ = ‖D.orthogonalVector‖ ^ 2 + ‖(D.cycleOffset : BoundaryHodgeStokesAmbient D.n) + k‖ ^ 2 := by
              simpa [pow_two, real_inner_comm, horth] using
                norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
        _ = ‖D.orthogonalVector‖ ^ 2 + ‖D.boundaryVector + k - D.orthogonalVector‖ ^ 2 := by
              congr 1
              rw [D.boundary_split]
              abel
    have hnonneg : 0 ≤ ‖D.boundaryVector + k - D.orthogonalVector‖ ^ 2 := sq_nonneg _
    nlinarith [hpyth, hnonneg, norm_nonneg D.orthogonalVector, norm_nonneg (D.boundaryVector + k)]

end

end Omega.Folding
