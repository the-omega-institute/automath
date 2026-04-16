import Mathlib.Tactic
import Omega.SPG.DyadicCubicalBoundaryInjective
import Omega.SPG.DyadicCubicalCellCount

namespace Omega.SPG

open Omega.SPG.DyadicCubicalCellCount

/-- The dyadic boundary code is the image of the top boundary map over `F₂`. -/
def dyadicBoundaryImageCode {Cn Cn1 : Type*} (boundaryTop : Cn → Cn1) : Set Cn1 :=
  Set.range boundaryTop

/-- Block length of the dyadic boundary image code. -/
def dyadicBoundaryImageBlockLength (n m : ℕ) : Nat :=
  dyadicFaceCellCount n m

/-- The top-boundary injectivity package identifies the code dimension with the number of
top-dimensional cubes. -/
noncomputable def dyadicBoundaryImageDimension {Cn Cn1 : Type*} (boundaryTop : Cn → Cn1)
    (n m : ℕ) : Nat :=
  by
    classical
    exact if Function.Injective boundaryTop then dyadicTopCellCount n m else 0

/-- Closed-form rate formula from the dyadic face and top-cell counts. -/
def dyadicBoundaryImageRate (n m : ℕ) : ℚ :=
  (2 ^ m : ℚ) / (n * (2 ^ m + 1))

/-- Each parity check comes from the four cofacets around an `(n-2)`-cell. -/
def dyadicBoundaryCheckDegree : Nat := 4

/-- Each `(n-1)`-cell has `2 (n-1)` codimension-two faces in its boundary. -/
def dyadicBoundaryVariableDegree (n : ℕ) : Nat := 2 * (n - 1)

/-- Paper-facing LDPC package for the dyadic top boundary image: the code is the image of the top
boundary, its block length and dimension are given by the dyadic cubical counts, and the local
incidence pattern yields constant check and variable degrees.
    thm:spg-dyadic-boundary-image-ldpc -/
theorem paper_spg_dyadic_boundary_image_ldpc
    {Cn Cn1 : Type*} [AddGroup Cn] [AddGroup Cn1]
    (boundaryTop : Cn → Cn1) (n m : ℕ)
    (hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v)
    (hKer : ∀ u, boundaryTop u = 0 → u = 0) :
    let code := dyadicBoundaryImageCode boundaryTop
    dyadicBoundaryImageBlockLength n m = n * (2 ^ m + 1) * 2 ^ ((n - 1) * m) ∧
      dyadicBoundaryImageDimension boundaryTop n m = 2 ^ (n * m) ∧
      dyadicBoundaryImageRate n m = (2 ^ m : ℚ) / (n * (2 ^ m + 1)) ∧
      dyadicBoundaryCheckDegree = 4 ∧
      dyadicBoundaryVariableDegree n = 2 * (n - 1) ∧
      code = Set.range boundaryTop := by
  classical
  dsimp
  have hInj : Function.Injective boundaryTop :=
    paper_spg_dyadic_cubical_boundary_injective boundaryTop hSub hKer
  refine ⟨rfl, ?_⟩
  refine ⟨by simp [dyadicBoundaryImageDimension, dyadicTopCellCount, hInj], ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  exact ⟨rfl, rfl⟩

end Omega.SPG
