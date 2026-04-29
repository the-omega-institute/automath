import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete F₂-linear invariance predicate for the center module in the window-`6`
characteristic-rigidity statement. The closure under linear endomorphisms is the local readout of
the full linear symmetry package: it lets a nonzero vector generate every target vector by a
rank-one linear map. -/
def conclusion_window6_center_characteristic_rigidity_GL8InvariantSubspace
    (W : Set (Fin 8 -> ZMod 2)) : Prop :=
  (0 : Fin 8 -> ZMod 2) ∈ W ∧
    (∀ x ∈ W, ∀ y ∈ W, x + y ∈ W) ∧
      ∀ T : (Fin 8 -> ZMod 2) →ₗ[ZMod 2] (Fin 8 -> ZMod 2), ∀ x ∈ W, T x ∈ W

/-- A nonzero vector in `(F₂)^8` has a nonzero coordinate. -/
lemma conclusion_window6_center_characteristic_rigidity_exists_nonzero_coord
    {x : Fin 8 -> ZMod 2} (hx : x ≠ 0) : ∃ i : Fin 8, x i ≠ 0 := by
  by_contra h
  push_neg at h
  exact hx (funext h)

/-- Rank-one map sending a chosen vector with nonzero `i`-coordinate to `y`. -/
noncomputable def conclusion_window6_center_characteristic_rigidity_rankOneMap
    (x y : Fin 8 -> ZMod 2) (i : Fin 8) :
    (Fin 8 -> ZMod 2) →ₗ[ZMod 2] (Fin 8 -> ZMod 2) where
  toFun z := ((x i)⁻¹ * z i) • y
  map_add' z z' := by
    ext j
    simp [mul_add]
    ring
  map_smul' c z := by
    ext j
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- The rank-one map sends its source vector to the prescribed target. -/
lemma conclusion_window6_center_characteristic_rigidity_rankOneMap_apply
    {x y : Fin 8 -> ZMod 2} {i : Fin 8} (hi : x i ≠ 0) :
    conclusion_window6_center_characteristic_rigidity_rankOneMap x y i x = y := by
  ext j
  simp [conclusion_window6_center_characteristic_rigidity_rankOneMap, inv_mul_cancel₀ hi]

/-- Paper label:
`thm:conclusion-window6-center-characteristic-rigidity`. Any nonzero invariant F₂-subspace of the
eight-dimensional center module contains every vector, while the zero case is exactly `{0}`. -/
theorem paper_conclusion_window6_center_characteristic_rigidity
    (W : Set (Fin 8 -> ZMod 2))
    (hW : conclusion_window6_center_characteristic_rigidity_GL8InvariantSubspace W) :
    W = {0} ∨ W = Set.univ := by
  rcases hW with ⟨hzero, _hadd, hlin⟩
  by_cases hOnlyZero : ∀ x ∈ W, x = 0
  · left
    ext x
    constructor
    · intro hx
      simp [hOnlyZero x hx]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      simpa [hx] using hzero
  · right
    push_neg at hOnlyZero
    rcases hOnlyZero with ⟨x, hxW, hxne⟩
    rcases conclusion_window6_center_characteristic_rigidity_exists_nonzero_coord hxne with
      ⟨i, hi⟩
    ext y
    constructor
    · intro _hy
      trivial
    · intro _hy
      let T := conclusion_window6_center_characteristic_rigidity_rankOneMap x y i
      have hTx :
          T x = y :=
        conclusion_window6_center_characteristic_rigidity_rankOneMap_apply (x := x) (y := y)
          (i := i) hi
      simpa [hTx] using hlin T x hxW

end Omega.Conclusion
