import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-!
# Geometric uplift (4+4) collapse

Under the strong local geometric uplift, the 8-fold parity superselection of
P₆ ≅ (ℤ/2ℤ)³ collapses to exactly two classes of 4 sectors each, determined
by the diagonal subgroup P₆^geo = ⟨(1,1,1)⟩ ≅ ℤ/2ℤ.

The restriction map P₆^hat → P₆^geo^hat ≅ {±1} has fibers of size exactly 4,
because exactly 4 of the 8 elements (a₁,a₂,a₃) ∈ (ℤ/2ℤ)³ have even parity
a₁ + a₂ + a₃ ≡ 0 (mod 2), and 4 have odd parity.

## Paper references

- cor:conclusion-window6-geometric-uplift-four-four-collapse
-/

namespace Omega.Conclusion.GeometricUpliftFourFourCollapse

/-! ## Parity counting in (ℤ/2ℤ)³ -/

/-- The total number of elements in (ℤ/2ℤ)³ is 8.
    cor:conclusion-window6-geometric-uplift-four-four-collapse -/
theorem z2_cube_card : (2 : ℕ) ^ 3 = 8 := by omega

/-- The number of even-parity triples (a₁+a₂+a₃ ≡ 0 mod 2) in {0,1}³ is 4.
    These are: (0,0,0), (0,1,1), (1,0,1), (1,1,0).
    cor:conclusion-window6-geometric-uplift-four-four-collapse -/
theorem even_parity_count :
    (Finset.univ.filter (fun v : Fin 2 × Fin 2 × Fin 2 =>
      (v.1.val + v.2.1.val + v.2.2.val) % 2 = 0)).card = 4 := by native_decide

/-- The number of odd-parity triples (a₁+a₂+a₃ ≡ 1 mod 2) in {0,1}³ is 4.
    These are: (0,0,1), (0,1,0), (1,0,0), (1,1,1).
    cor:conclusion-window6-geometric-uplift-four-four-collapse -/
theorem odd_parity_count :
    (Finset.univ.filter (fun v : Fin 2 × Fin 2 × Fin 2 =>
      (v.1.val + v.2.1.val + v.2.2.val) % 2 = 1)).card = 4 := by native_decide

/-- The (4+4) partition is exhaustive: 4 + 4 = 8 = |(ℤ/2ℤ)³|.
    cor:conclusion-window6-geometric-uplift-four-four-collapse -/
theorem four_plus_four_exhaustive : 4 + 4 = (2 : ℕ) ^ 3 := by omega

/-- The fibers have equal size: both fibers of the restriction map have 4 elements.
    cor:conclusion-window6-geometric-uplift-four-four-collapse -/
theorem paper_conclusion_geometric_uplift_four_four_collapse :
    (Finset.univ.filter (fun v : Fin 2 × Fin 2 × Fin 2 =>
      (v.1.val + v.2.1.val + v.2.2.val) % 2 = 0)).card = 4 ∧
    (Finset.univ.filter (fun v : Fin 2 × Fin 2 × Fin 2 =>
      (v.1.val + v.2.1.val + v.2.2.val) % 2 = 1)).card = 4 := by
  exact ⟨by native_decide, by native_decide⟩

end Omega.Conclusion.GeometricUpliftFourFourCollapse
