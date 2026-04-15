import Mathlib.Tactic
import Omega.Folding.MomentSum

namespace Omega.Conclusion

/-- Chapter-local `x`-summand of the Morita defect tensor decomposition. -/
noncomputable def collisionMomentMoritaSummand (q m : ℕ) (x : Omega.X m) : ℕ :=
  (Omega.X.fiberMultiplicity x) ^ q

/-- The chapter-local hom-dimension is the fiberwise `q`-moment sum. -/
noncomputable def collisionMomentMoritaHomDim (q m : ℕ) : ℕ :=
  ∑ x : Omega.X m, collisionMomentMoritaSummand q m x

/-- The lightweight tensor decomposition: summing the `x`-summands recovers the hom-dimension. -/
def collisionMomentMoritaTensorDecomposition (q m : ℕ) : Prop :=
  collisionMomentMoritaHomDim q m =
    ∑ x : Omega.X m, collisionMomentMoritaSummand q m x

/-- Paper-facing Morita defect tensor decomposition and the resulting moment identity.
    prop:conclusion-collision-moment-morita-defect-fusion -/
theorem paper_conclusion_collision_moment_morita_defect_fusion (q m : ℕ) (hq : 1 ≤ q) :
    collisionMomentMoritaTensorDecomposition q m ∧
      collisionMomentMoritaHomDim q m = Omega.momentSum q m := by
  let _ := hq
  refine ⟨?_, ?_⟩
  · simp [collisionMomentMoritaTensorDecomposition, collisionMomentMoritaHomDim]
  · simp [collisionMomentMoritaHomDim, collisionMomentMoritaSummand, Omega.momentSum]

end Omega.Conclusion
