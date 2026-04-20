import Mathlib.Tactic

namespace Omega.GroupUnification

/-- The transported root `w = r z + r⁻¹ z⁻¹`. -/
def groupJGTransportedRoot {K : Type*} [Field K] (r z : K) : K :=
  r * z + r⁻¹ * z⁻¹

/-- The reciprocal companion root of the transport quadratic. -/
def groupJGReciprocalCompanion {K : Type*} [Field K] (r z : K) : K :=
  r⁻¹ * r⁻¹ * z⁻¹

/-- The quadratic that links the transported root back to the original root. -/
def groupJGTransportQuadratic {K : Type*} [Field K] (r w z : K) : K :=
  r * z ^ 2 - w * z + r⁻¹

lemma groupJGTransportQuadratic_factor {K : Type*} [Field K]
    (r z x : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    groupJGTransportQuadratic r (groupJGTransportedRoot r z) x =
      r * (x - z) * (x - groupJGReciprocalCompanion r z) := by
  unfold groupJGTransportQuadratic groupJGTransportedRoot groupJGReciprocalCompanion
  field_simp [hr, hz]
  ring_nf

lemma groupJGTransportQuadratic_root_iff {K : Type*} [Field K]
    (r z x : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    groupJGTransportQuadratic r (groupJGTransportedRoot r z) x = 0 ↔
      x = z ∨ x = groupJGReciprocalCompanion r z := by
  rw [groupJGTransportQuadratic_factor r z x hr hz]
  constructor
  · intro h
    have h' : r * ((x - z) * (x - groupJGReciprocalCompanion r z)) = 0 := by
      simpa [mul_assoc] using h
    rcases mul_eq_zero.mp h' with hr0 | hrest
    · exact (hr hr0).elim
    · rcases mul_eq_zero.mp hrest with hx | hcomp
      · exact Or.inl (sub_eq_zero.mp hx)
      · exact Or.inr (sub_eq_zero.mp hcomp)
  · rintro (hEq | hEq)
    · simp [hEq]
    · simp [hEq]

/-- Lossless recovery on the transported roots: the transport quadratic recovers each original
root uniquely inside the original root family once the reciprocal companion is excluded.
    thm:group-jg-transcendental-galois-lossless -/
theorem paper_group_jg_transcendental_galois_lossless
    {K : Type*} [Field K]
    (r : K) (hr : r ≠ 0) {n : Nat} (roots : Fin n → K)
    (hroot0 : ∀ i, roots i ≠ 0)
    (hinj : Function.Injective roots)
    (hnoReciprocal : ∀ i j, groupJGReciprocalCompanion r (roots i) ≠ roots j) :
    let transported : Fin n → K := fun i => groupJGTransportedRoot r (roots i)
    (∀ i, groupJGTransportQuadratic r (transported i) (roots i) = 0) ∧
      (∀ i j, groupJGTransportQuadratic r (transported i) (roots j) = 0 → i = j) := by
  dsimp
  constructor
  · intro i
    exact (groupJGTransportQuadratic_root_iff r (roots i) (roots i) hr (hroot0 i)).2 (Or.inl rfl)
  · intro i j hQuad
    have hRoot := (groupJGTransportQuadratic_root_iff r (roots i) (roots j) hr (hroot0 i)).1 hQuad
    cases hRoot with
    | inl hEq =>
        exact hinj hEq.symm
    | inr hEq =>
        exact False.elim (hnoReciprocal i j hEq.symm)

end Omega.GroupUnification
