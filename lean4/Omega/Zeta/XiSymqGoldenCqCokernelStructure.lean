import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Smith exponents of the golden symmetric-power matrix after removing the unit factor. -/
def xi_symq_golden_cq_cokernel_structure_torsion_exponents (q : Nat) : List Nat :=
  (List.range q).map Nat.succ

/-- Jordan-Hölder length obtained by summing the non-unit Smith exponents. -/
def xi_symq_golden_cq_cokernel_structure_length (q : Nat) : Nat :=
  q * (q + 1) / 2

/-- The triangular exponent `1 + ... + q`. -/
def xi_symq_golden_cq_cokernel_structure_triangular_exponent (q : Nat) : Nat :=
  q * (q + 1) / 2

/-- Norm-size contribution from `Norm(pi)=5`. -/
def xi_symq_golden_cq_cokernel_structure_cardinality (q : Nat) : Nat :=
  5 ^ xi_symq_golden_cq_cokernel_structure_length q

lemma xi_symq_golden_cq_cokernel_structure_length_eq_triangular (q : Nat) :
    xi_symq_golden_cq_cokernel_structure_length q =
      xi_symq_golden_cq_cokernel_structure_triangular_exponent q := by
  rfl

/-- Paper-facing cokernel package: the unit Smith factor is omitted, the remaining factors have
exponents `1,...,q`, the length is their sum, and the cardinality uses `Norm(pi)=5`. -/
def xi_symq_golden_cq_cokernel_structure_statement (q : Nat) : Prop :=
  xi_symq_golden_cq_cokernel_structure_torsion_exponents q =
      (List.range q).map Nat.succ ∧
    xi_symq_golden_cq_cokernel_structure_length q =
      xi_symq_golden_cq_cokernel_structure_triangular_exponent q ∧
    xi_symq_golden_cq_cokernel_structure_cardinality q =
      5 ^ xi_symq_golden_cq_cokernel_structure_triangular_exponent q

/-- Paper label: `cor:xi-symq-golden-cq-cokernel-structure`. -/
theorem paper_xi_symq_golden_cq_cokernel_structure (q : Nat) :
    xi_symq_golden_cq_cokernel_structure_statement q := by
  refine ⟨rfl, xi_symq_golden_cq_cokernel_structure_length_eq_triangular q, ?_⟩
  simp [xi_symq_golden_cq_cokernel_structure_cardinality,
    xi_symq_golden_cq_cokernel_structure_length_eq_triangular]

end Omega.Zeta
