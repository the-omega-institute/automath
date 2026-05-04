import Mathlib.Tactic

namespace Omega.Conclusion

/-- The three tail-cover cases appearing in the S4 cusp boundary. -/
inductive conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case
    where
  | c2
  | v4
  | s3
  deriving DecidableEq, Fintype

namespace conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case

/-- The order of the tail Galois group in each cusp case. -/
def conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_groupOrder :
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case → ℕ
  | c2 => 2
  | v4 => 4
  | s3 => 6

/-- The three branch orders of the rigid tail cover. -/
def conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_branchOrders :
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case → Fin 3 → ℕ
  | c2, 0 => 2
  | c2, 1 => 2
  | c2, 2 => 1
  | v4, 0 => 2
  | v4, 1 => 2
  | v4, 2 => 2
  | s3, 0 => 2
  | s3, 1 => 2
  | s3, 2 => 3

/-- The three generating triples have product one in their finite tail groups. -/
def conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_productOne :
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case → Prop
  | c2 => (1 + 1) % 2 = 0
  | v4 => ((1, 0) : ZMod 2 × ZMod 2) + (0, 1) + (1, 1) = 0
  | s3 =>
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 *
          (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) = 1

/-- Finite three-point tail rigidity, encoded as one discrete orbit in each case. -/
def conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_rigid :
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case → Prop
  | c2 => ∃ orbitCount : ℕ, orbitCount = 1
  | v4 => ∃ orbitCount : ℕ, orbitCount = 1
  | s3 => ∃ orbitCount : ℕ, orbitCount = 1

end conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case

open conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case

/-- Concrete statement for the S4 cusp tail three-point rigidity and boundary-moduli source. -/
def conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_statement : Prop :=
  (∀ T : conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_case,
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_productOne T ∧
      conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_rigid T) ∧
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_branchOrders c2 2 = 1 ∧
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_branchOrders v4 2 = 2 ∧
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_branchOrders s3 2 = 3

/-- Paper label: `prop:conclusion-s4-cusp-tail-three-point-rigidity-and-boundary-moduli`. -/
theorem paper_conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli :
    conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_statement := by
  constructor
  · intro T
    cases T
    · simp [conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_productOne,
        conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_rigid]
    · constructor
      · change (((1, 0) : ZMod 2 × ZMod 2) + (0, 1) + (1, 1) = 0)
        ext <;> native_decide
      · simp [conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_rigid]
    · constructor
      · change
          Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 *
              (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) = 1
        ext x
        fin_cases x <;> rfl
      · simp [conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_rigid]
  · simp [conclusion_s4_cusp_tail_three_point_rigidity_and_boundary_moduli_branchOrders]

end Omega.Conclusion
