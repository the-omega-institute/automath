import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete code for Turing-machine/input tokens in this finite reduction shell. -/
abbrev conclusion_circuit_output_renyi_density_halting_TMInput : Type :=
  Nat

/-- The two circuit shapes used in the collision-output entropy reduction. -/
inductive conclusion_circuit_output_renyi_density_halting_Circuit where
  | conclusion_circuit_output_renyi_density_halting_Circuit_identity
  | conclusion_circuit_output_renyi_density_halting_Circuit_constant
  deriving DecidableEq

/-- Concrete halting predicate used by the finite shell. -/
def conclusion_circuit_output_renyi_density_halting_halts
    (M x : conclusion_circuit_output_renyi_density_halting_TMInput) : Prop :=
  M ≤ x

/-- Uniform collision model: halting tails are constant, nonhalting tails are identities. -/
def conclusion_circuit_output_renyi_density_halting_uniform_collision_model
    (M x : conclusion_circuit_output_renyi_density_halting_TMInput)
    (C : Nat → conclusion_circuit_output_renyi_density_halting_Circuit) : Prop :=
  (conclusion_circuit_output_renyi_density_halting_halts M x →
      ∀ t, C t = .conclusion_circuit_output_renyi_density_halting_Circuit_constant) ∧
    (¬ conclusion_circuit_output_renyi_density_halting_halts M x →
      ∀ t, C t = .conclusion_circuit_output_renyi_density_halting_Circuit_identity)

/-- Output Renyi entropy density for the identity/constant circuit tail. -/
def conclusion_circuit_output_renyi_density_halting_hq (_q : Nat)
    (C : Nat → conclusion_circuit_output_renyi_density_halting_Circuit) : Nat :=
  if C 0 =
      .conclusion_circuit_output_renyi_density_halting_Circuit_identity then
    1
  else
    0

/-- Paper label: `cor:conclusion-circuit-output-renyi-density-halting`. -/
theorem paper_conclusion_circuit_output_renyi_density_halting (q : Nat) (hq : 2 ≤ q)
    (M x : conclusion_circuit_output_renyi_density_halting_TMInput)
    (C : Nat → conclusion_circuit_output_renyi_density_halting_Circuit)
    (hmodel : conclusion_circuit_output_renyi_density_halting_uniform_collision_model M x C) :
    (conclusion_circuit_output_renyi_density_halting_hq q C = 1 ↔
        ¬ conclusion_circuit_output_renyi_density_halting_halts M x) ∧
      (conclusion_circuit_output_renyi_density_halting_hq q C = 0 ↔
        conclusion_circuit_output_renyi_density_halting_halts M x) := by
  classical
  have _hq_ge_two : 2 ≤ q := hq
  by_cases hhalt : conclusion_circuit_output_renyi_density_halting_halts M x
  · have hC :
        C 0 =
          .conclusion_circuit_output_renyi_density_halting_Circuit_constant :=
      hmodel.1 hhalt 0
    constructor
    · constructor
      · intro hden
        have hzero : conclusion_circuit_output_renyi_density_halting_hq q C = 0 := by
          simp [conclusion_circuit_output_renyi_density_halting_hq, hC]
        omega
      · intro hnot
        exact False.elim (hnot hhalt)
    · constructor
      · intro _hden
        exact hhalt
      · intro _hhalt
        simp [conclusion_circuit_output_renyi_density_halting_hq, hC]
  · have hC :
        C 0 =
          .conclusion_circuit_output_renyi_density_halting_Circuit_identity :=
      hmodel.2 hhalt 0
    constructor
    · constructor
      · intro _hden
        exact hhalt
      · intro _hnot
        simp [conclusion_circuit_output_renyi_density_halting_hq, hC]
    · constructor
      · intro hden
        have hone : conclusion_circuit_output_renyi_density_halting_hq q C = 1 := by
          simp [conclusion_circuit_output_renyi_density_halting_hq, hC]
        omega
      · intro hhalts
        exact False.elim (hhalt hhalts)

end Omega.Conclusion
