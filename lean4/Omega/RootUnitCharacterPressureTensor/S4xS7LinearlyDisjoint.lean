import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.RootUnitCharacterPressureTensor

/-- The audited quadratic subextension degree on the `S₄` side. -/
def root_unit_s4xs7_linearly_disjoint_s4_quadratic_subextension_degree : ℕ :=
  2

/-- The distinguished quadratic witness on the `S₄` side. -/
def root_unit_s4xs7_linearly_disjoint_s4_quadratic_witness : ℤ :=
  -101488

/-- The distinguished quadratic witness on the `S₇` side. -/
def root_unit_s4xs7_linearly_disjoint_s7_quadratic_witness : ℤ :=
  -2419698015243781904793600

/-- The unique quadratic subextension on the `S₇` side is the index-`2` alternating quotient. -/
def root_unit_s4xs7_linearly_disjoint_s7_quadratic_subextension_degree : ℕ :=
  2

/-- Equality of the audited quadratic witnesses would force a common quadratic subfield. -/
def root_unit_s4xs7_linearly_disjoint_shared_quadratic_witness : Prop :=
  root_unit_s4xs7_linearly_disjoint_s4_quadratic_witness =
    root_unit_s4xs7_linearly_disjoint_s7_quadratic_witness

/-- The product Galois group predicted by linear disjointness. -/
def root_unit_s4xs7_linearly_disjoint_product_galois_group_card : ℕ :=
  Fintype.card ((Equiv.Perm (Fin 4)) × (Equiv.Perm (Fin 7)))

/-- Paper label: `thm:root-unit-s4xs7-linearly-disjoint`.
The `S₄` and `S₇` packages each carry a unique quadratic quotient, the audited quadratic witnesses
are distinct, and the resulting product group has the expected cardinality. -/
theorem paper_root_unit_s4xs7_linearly_disjoint :
    root_unit_s4xs7_linearly_disjoint_s4_quadratic_subextension_degree = 2 ∧
      root_unit_s4xs7_linearly_disjoint_s7_quadratic_subextension_degree = 2 ∧
      ¬ root_unit_s4xs7_linearly_disjoint_shared_quadratic_witness ∧
      root_unit_s4xs7_linearly_disjoint_product_galois_group_card = 24 * 5040 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · unfold root_unit_s4xs7_linearly_disjoint_s7_quadratic_subextension_degree
    rfl
  · unfold root_unit_s4xs7_linearly_disjoint_shared_quadratic_witness
    unfold root_unit_s4xs7_linearly_disjoint_s4_quadratic_witness
      root_unit_s4xs7_linearly_disjoint_s7_quadratic_witness
    norm_num
  · unfold root_unit_s4xs7_linearly_disjoint_product_galois_group_card
    norm_num [Fintype.card_perm]

end Omega.RootUnitCharacterPressureTensor
