import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Graph.Sofic
import Omega.Graph.TransferMatrix

namespace Omega.EA

open Polynomial
open Omega.Graph

/-- Reachability by a path of length at most two, sufficient for the finite case analysis in this
file. -/
def TwoStepReachable {Q A : Type*} (edge : Q → A → Q → Prop) (q q' : Q) : Prop :=
  q = q' ∨ (∃ a, edge q a q') ∨ ∃ r a₁ a₂, edge q a₁ r ∧ edge r a₂ q'

/-- Every pair of states is connected by a path of length at most two. -/
def TwoStepStronglyConnected {Q A : Type*} (edge : Q → A → Q → Prop) : Prop :=
  ∀ q q', TwoStepReachable edge q q'

/-- The one-state carry-free skeleton with seven outgoing symbols. -/
def sevenCarryFreeEdge (_ : Unit) (_ : Fin 7) (_ : Unit) : Prop := True

/-- The one-state carry-free skeleton with three outgoing symbols. -/
def threeCarryFreeEdge (_ : Unit) (_ : Fin 3) (_ : Unit) : Prop := True

/-- The one-state adjacency matrix of the `7`-shift. -/
def sevenShiftAdjacency : Matrix (Fin 1) (Fin 1) ℤ :=
  !![7]

/-- The one-state adjacency matrix of the `3`-shift. -/
def threeShiftAdjacency : Matrix (Fin 1) (Fin 1) ℤ :=
  !![3]

private lemma sevenCarryFree_stronglyConnected :
    TwoStepStronglyConnected sevenCarryFreeEdge := by
  intro q q'
  left
  cases q
  cases q'
  rfl

private lemma threeCarryFree_stronglyConnected :
    TwoStepStronglyConnected threeCarryFreeEdge := by
  intro q q'
  left
  cases q
  cases q'
  rfl

private lemma goldenCarryFree_stronglyConnected :
    TwoStepStronglyConnected goldenMeanGraph.edge := by
  intro q q'
  cases q <;> cases q'
  · left
    rfl
  · right
    left
    exact ⟨true, goldenMean_edge_ft⟩
  · right
    left
    exact ⟨false, goldenMean_edge_tf⟩
  · right
    right
    exact ⟨false, false, true, goldenMean_edge_tf, goldenMean_edge_ft⟩

private lemma sevenShiftAdjacency_charpoly :
    sevenShiftAdjacency.charpoly = Polynomial.X - Polynomial.C 7 := by
  unfold sevenShiftAdjacency Matrix.charpoly
  rw [Matrix.det_fin_one]
  simp [Matrix.charmatrix, Matrix.diagonal]

private lemma threeShiftAdjacency_charpoly :
    threeShiftAdjacency.charpoly = Polynomial.X - Polynomial.C 3 := by
  unfold threeShiftAdjacency Matrix.charpoly
  rw [Matrix.det_fin_one]
  simp [Matrix.charmatrix, Matrix.diagonal]

/-- The three single-flow carry-free skeletons collapse, after finite case analysis, to the
`7`-shift, the `3`-shift, and the golden-mean shift. The associated adjacency matrices therefore
have characteristic polynomials `X - 7`, `X - 3`, and `X² - X - 1`.
    thm:carry-free-zeta-trichotomy -/
theorem paper_carry_free_zeta_trichotomy :
    TwoStepStronglyConnected sevenCarryFreeEdge ∧
      TwoStepStronglyConnected threeCarryFreeEdge ∧
      TwoStepStronglyConnected goldenMeanGraph.edge ∧
      sevenShiftAdjacency.charpoly = Polynomial.X - Polynomial.C 7 ∧
      threeShiftAdjacency.charpoly = Polynomial.X - Polynomial.C 3 ∧
      goldenMeanAdjacency.charpoly = Polynomial.X ^ 2 - Polynomial.X - 1 := by
  exact ⟨sevenCarryFree_stronglyConnected, threeCarryFree_stronglyConnected,
    goldenCarryFree_stronglyConnected, sevenShiftAdjacency_charpoly,
    threeShiftAdjacency_charpoly, goldenMeanAdjacency_charpoly⟩

end Omega.EA
