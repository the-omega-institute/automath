import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Coordinate kernels on the period-`3` fiber after identifying the fiber with `{0,1}^n`. -/
def conclusion_period3_fiber_coordinate_lattice_booleanization_kernel (n : Nat)
    (S : Finset (Fin n)) (x y : Fin n → Bool) : Prop :=
  ∀ j, j ∈ S → x j = y j

/-- The coordinate quotient order: remembering more coordinates gives a finer quotient. -/
def conclusion_period3_fiber_coordinate_lattice_booleanization_order (n : Nat)
    (S T : Finset (Fin n)) : Prop :=
  S ⊆ T

/-- Boolean-lattice Möbius function for coordinate quotients. -/
def conclusion_period3_fiber_coordinate_lattice_booleanization_mobius (n : Nat)
    (S T : Finset (Fin n)) : Int :=
  if S ⊆ T then (-1 : Int) ^ (T \ S).card else 0

/-- Concrete Booleanization package for the coordinate quotient lattice of the period-`3` fiber. -/
def conclusion_period3_fiber_coordinate_lattice_booleanization_statement (n : Nat) : Prop :=
  (∀ S T : Finset (Fin n),
      (∀ x y : Fin n → Bool,
          conclusion_period3_fiber_coordinate_lattice_booleanization_kernel n T x y →
            conclusion_period3_fiber_coordinate_lattice_booleanization_kernel n S x y) ↔
        conclusion_period3_fiber_coordinate_lattice_booleanization_order n S T) ∧
    (∀ S T : Finset (Fin n),
      conclusion_period3_fiber_coordinate_lattice_booleanization_order n S T →
        conclusion_period3_fiber_coordinate_lattice_booleanization_mobius n S T =
          (-1 : Int) ^ (T \ S).card) ∧
    conclusion_period3_fiber_coordinate_lattice_booleanization_mobius n ∅ Finset.univ =
      (-1 : Int) ^ n

/-- Paper label: `thm:conclusion-period3-fiber-coordinate-lattice-booleanization`. The
coordinate quotients of the period-`3` fiber are ordered exactly by coordinate inclusion, and the
resulting Boolean lattice has the standard Möbius function. -/
theorem paper_conclusion_period3_fiber_coordinate_lattice_booleanization (n : Nat) :
    conclusion_period3_fiber_coordinate_lattice_booleanization_statement n := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro S T
    constructor
    · intro h j hjS
      by_contra hjT
      let x : Fin n → Bool := fun _ => false
      let y : Fin n → Bool := fun k => if k = j then true else false
      have hkerT :
          conclusion_period3_fiber_coordinate_lattice_booleanization_kernel n T x y := by
        intro k hkT
        have hkj : k ≠ j := by
          intro hkj
          subst hkj
          exact hjT hkT
        simp [x, y, hkj]
      have hkerS := h x y hkerT
      have hj_eq := hkerS j hjS
      simp [x, y] at hj_eq
    · intro hST x y hkerT j hjS
      exact hkerT j (hST hjS)
  · intro S T hST
    unfold conclusion_period3_fiber_coordinate_lattice_booleanization_order at hST
    simp [conclusion_period3_fiber_coordinate_lattice_booleanization_mobius, hST]
  · simp [conclusion_period3_fiber_coordinate_lattice_booleanization_mobius]

end Omega.Conclusion
