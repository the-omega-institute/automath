import Mathlib.Tactic

namespace Omega.Zeta

/-- The 18 cyclic window-`6` words appearing in the `C₃` root dictionary. -/
inductive xi_window6_c3_cyclic_fiber_trisection_Word
  | w000000
  | w100000
  | w010000
  | w001000
  | w101000
  | w000100
  | w100100
  | w010100
  | w000010
  | w100010
  | w010010
  | w001010
  | w101010
  | w000001
  | w010001
  | w001001
  | w000101
  | w010101
  deriving DecidableEq, Fintype, Repr

/-- The `C₃` root coordinates attached to the 18 cyclic words. -/
abbrev xi_window6_c3_cyclic_fiber_trisection_Root := ℤ × ℤ × ℤ

/-- The explicit `C₃` root dictionary from the paper's window-`6` table. -/
def xi_window6_c3_cyclic_fiber_trisection_root :
    xi_window6_c3_cyclic_fiber_trisection_Word →
      xi_window6_c3_cyclic_fiber_trisection_Root
  | .w000000 => (1, 1, 0)
  | .w100000 => (2, 0, 0)
  | .w010000 => (0, 2, 0)
  | .w001000 => (0, 0, 2)
  | .w101000 => (1, -1, 0)
  | .w000100 => (0, 0, -2)
  | .w100100 => (-1, 1, 0)
  | .w010100 => (-1, -1, 0)
  | .w000010 => (0, -2, 0)
  | .w100010 => (1, 0, 1)
  | .w010010 => (1, 0, -1)
  | .w001010 => (-1, 0, 1)
  | .w101010 => (-1, 0, -1)
  | .w000001 => (-2, 0, 0)
  | .w010001 => (0, 1, 1)
  | .w001001 => (0, 1, -1)
  | .w000101 => (0, -1, 1)
  | .w010101 => (0, -1, -1)

/-- The exact window-`6` multiplicity table on cyclic words. -/
def xi_window6_c3_cyclic_fiber_trisection_multiplicity :
    xi_window6_c3_cyclic_fiber_trisection_Word → ℕ
  | .w000000 => 4
  | .w100000 => 4
  | .w010000 => 4
  | .w001000 => 4
  | .w101000 => 4
  | .w000100 => 4
  | .w100100 => 4
  | .w010100 => 4
  | .w000010 => 4
  | .w100010 => 3
  | .w010010 => 3
  | .w001010 => 3
  | .w101010 => 3
  | .w000001 => 2
  | .w010001 => 2
  | .w001001 => 2
  | .w000101 => 2
  | .w010101 => 2

/-- The cyclic words whose fibers have multiplicity `j`. -/
def xi_window6_c3_cyclic_fiber_trisection_layer (j : ℕ) :
    Finset xi_window6_c3_cyclic_fiber_trisection_Word :=
  Finset.univ.filter fun w => xi_window6_c3_cyclic_fiber_trisection_multiplicity w = j

/-- The explicit long-root slice corresponding to multiplicity `4`. -/
def xi_window6_c3_cyclic_fiber_trisection_roots4 :
    Finset xi_window6_c3_cyclic_fiber_trisection_Root :=
  {(2, 0, 0), (0, 2, 0), (0, -2, 0), (0, 0, 2), (0, 0, -2),
    (1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0)}

/-- The explicit middle slice corresponding to multiplicity `3`. -/
def xi_window6_c3_cyclic_fiber_trisection_roots3 :
    Finset xi_window6_c3_cyclic_fiber_trisection_Root :=
  {(1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1)}

/-- The explicit minimal-fiber slice corresponding to multiplicity `2`. -/
def xi_window6_c3_cyclic_fiber_trisection_roots2 :
    Finset xi_window6_c3_cyclic_fiber_trisection_Root :=
  {(-2, 0, 0), (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)}

/-- Paper label: `thm:xi-window6-c3-cyclic-fiber-trisection`. -/
theorem paper_xi_window6_c3_cyclic_fiber_trisection :
    Finset.image xi_window6_c3_cyclic_fiber_trisection_root
        (xi_window6_c3_cyclic_fiber_trisection_layer 4) =
      xi_window6_c3_cyclic_fiber_trisection_roots4 ∧
    Finset.image xi_window6_c3_cyclic_fiber_trisection_root
        (xi_window6_c3_cyclic_fiber_trisection_layer 3) =
      xi_window6_c3_cyclic_fiber_trisection_roots3 ∧
    Finset.image xi_window6_c3_cyclic_fiber_trisection_root
        (xi_window6_c3_cyclic_fiber_trisection_layer 2) =
      xi_window6_c3_cyclic_fiber_trisection_roots2 ∧
    (xi_window6_c3_cyclic_fiber_trisection_layer 4).card = 9 ∧
    (xi_window6_c3_cyclic_fiber_trisection_layer 3).card = 4 ∧
    (xi_window6_c3_cyclic_fiber_trisection_layer 2).card = 5 := by
  decide

end Omega.Zeta
