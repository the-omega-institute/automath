import Mathlib.Tactic

namespace Omega.Conclusion

/-- The common concrete halting-time budget: `none` is the infinite halting-time branch, while
`some T` records a finite halt at time `T`. -/
def conclusion_halting_fourfold_complexity_identity_time_budget : Option ℕ → ℕ
  | none => 1
  | some T => T + 1

/-- The binary register count associated to the same halting-time budget. -/
def conclusion_halting_fourfold_complexity_identity_register_budget : Option ℕ → ℕ
  | none => 0
  | some T => Nat.clog 2 (T + 1)

/-- Concrete data for the fourfold identity. The equality fields are the already-established exact
formulas for the time depth, external budget, state count, collision realization dimension, and
binary register encoding bound. -/
structure conclusion_halting_fourfold_complexity_identity_data where
  halting_time : Option ℕ
  q : ℕ
  hq : 2 ≤ q
  time_depth : ℕ
  external_budget : ℕ
  state_complexity : ℕ
  collision_dimension : ℕ
  binary_registers : ℕ
  time_depth_eq :
    time_depth = conclusion_halting_fourfold_complexity_identity_time_budget halting_time
  external_budget_eq :
    external_budget = conclusion_halting_fourfold_complexity_identity_time_budget halting_time
  state_complexity_eq :
    state_complexity = conclusion_halting_fourfold_complexity_identity_time_budget halting_time
  collision_dimension_eq :
    collision_dimension = conclusion_halting_fourfold_complexity_identity_time_budget halting_time
  binary_registers_eq :
    binary_registers = conclusion_halting_fourfold_complexity_identity_register_budget halting_time

/-- Paper-facing fourfold complexity statement: all four concrete complexity measures are the same
halting-time budget, and the binary register count is its base-2 ceiling. -/
def conclusion_halting_fourfold_complexity_identity_statement
    (D : conclusion_halting_fourfold_complexity_identity_data) : Prop :=
  D.time_depth = D.external_budget ∧
    D.external_budget = D.state_complexity ∧
    D.state_complexity = D.collision_dimension ∧
    D.collision_dimension =
      conclusion_halting_fourfold_complexity_identity_time_budget D.halting_time ∧
    D.binary_registers =
      conclusion_halting_fourfold_complexity_identity_register_budget D.halting_time

/-- Paper label: `thm:conclusion-halting-fourfold-complexity-identity`. -/
theorem paper_conclusion_halting_fourfold_complexity_identity
    (D : conclusion_halting_fourfold_complexity_identity_data) :
    conclusion_halting_fourfold_complexity_identity_statement D := by
  cases D.halting_time with
  | none =>
      simp [conclusion_halting_fourfold_complexity_identity_statement,
        conclusion_halting_fourfold_complexity_identity_time_budget,
        conclusion_halting_fourfold_complexity_identity_register_budget, D.time_depth_eq,
        D.external_budget_eq, D.state_complexity_eq, D.collision_dimension_eq,
        D.binary_registers_eq]
  | some T =>
      simp [conclusion_halting_fourfold_complexity_identity_statement,
        conclusion_halting_fourfold_complexity_identity_time_budget,
        conclusion_halting_fourfold_complexity_identity_register_budget, D.time_depth_eq,
        D.external_budget_eq, D.state_complexity_eq, D.collision_dimension_eq,
        D.binary_registers_eq]

end Omega.Conclusion
