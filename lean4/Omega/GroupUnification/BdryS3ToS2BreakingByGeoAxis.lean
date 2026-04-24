import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- The stabilizer of a chosen boundary axis inside the `S₃` permutation action. -/
abbrev boundaryAxisStabilizer (i : Fin 3) := { σ : Equiv.Perm (Fin 3) // σ i = i }

private def boundaryAxisStabilizerEquivFixedComplement (i : Fin 3) :
    boundaryAxisStabilizer i ≃
      { σ : Equiv.Perm (Fin 3) // ∀ a : Fin 3, ¬ (a ≠ i) → σ a = a } := by
  refine Equiv.subtypeEquivRight ?_
  intro σ
  constructor
  · intro h a ha
    have hEq : a = i := by simpa using ha
    simpa [hEq] using h
  · intro h
    exact h i (by simp)

/-- Fixing one axis in `S₃` leaves exactly the permutations of the complementary two axes, hence a
canonical equivalence with `Perm (Fin 2)`.
    prop:bdry-s3-to-s2-breaking-by-geo-axis -/
theorem paper_bdry_s3_to_s2_breaking_by_geo_axis (i : Fin 3) :
    Nonempty ({σ : Equiv.Perm (Fin 3) // σ i = i} ≃ Equiv.Perm (Fin 2)) := by
  classical
  let e₂ : Fin 2 ≃ { x : Fin 3 // x ≠ i } := finSuccAboveEquiv i
  refine ⟨(boundaryAxisStabilizerEquivFixedComplement i).trans ?_⟩
  exact (Equiv.Perm.subtypeEquivSubtypePerm fun a : Fin 3 => a ≠ i).symm.trans e₂.permCongr.symm

end Omega.GroupUnification
