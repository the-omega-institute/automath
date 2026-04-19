import Mathlib.Data.Fintype.Card
import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Concrete path-length data for the fence-factor representation of a fiber. -/
structure PomFiberFenceData where
  lengths : List ℕ

/-- The product of Fibonacci-cube factors associated to the path decomposition. -/
abbrev PomFiberFenceData.fiberProduct (D : PomFiberFenceData) : Type :=
  (i : Fin D.lengths.length) → Omega.X (D.lengths.get i)

/-- The product of fence-ideal factors, identified componentwise with path independent sets. -/
abbrev PomFiberFenceData.fenceIdealProduct (D : PomFiberFenceData) : Type :=
  (i : Fin D.lengths.length) → PathIndSets (D.lengths.get i)

/-- Componentwise Birkhoff representation: every path factor is identified with the corresponding
fence-ideal factor, and hence so is the full finite product. -/
def PomFiberFenceData.hasBirkhoffFenceIdealRepresentation (D : PomFiberFenceData) : Prop :=
  Nonempty (D.fiberProduct ≃ D.fenceIdealProduct) ∧
    Fintype.card D.fiberProduct = Fintype.card D.fenceIdealProduct

/-- The fiber/Fibonacci-cube factorization identifies each path component with independent sets on
that path; viewing those independent sets as fence ideals gives the componentwise Birkhoff model,
and taking the product over the disjoint-union decomposition yields the full representation.
    thm:pom-fiber-birkhoff-fence-ideal-lattice -/
theorem paper_pom_fiber_birkhoff_fence_ideal_lattice (D : PomFiberFenceData) :
    D.hasBirkhoffFenceIdealRepresentation := by
  let e : D.fiberProduct ≃ D.fenceIdealProduct :=
    { toFun := fun x i => xEquivPathIndSet (D.lengths.get i) (x i)
      invFun := fun y i => (xEquivPathIndSet (D.lengths.get i)).symm (y i)
      left_inv := by
        intro x
        funext i
        exact (xEquivPathIndSet (D.lengths.get i)).symm_apply_apply (x i)
      right_inv := by
        intro y
        funext i
        exact (xEquivPathIndSet (D.lengths.get i)).apply_symm_apply (y i) }
  refine ⟨⟨e⟩, ?_⟩
  exact Fintype.card_congr e

end Omega.POM
