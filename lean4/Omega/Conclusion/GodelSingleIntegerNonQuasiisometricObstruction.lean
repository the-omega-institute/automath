import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete lower code-length model for single-integer Gödelization at scale `m`. -/
def conclusion_godel_single_integer_non_quasiisometric_obstruction_godel_length
    (m : Nat) : Nat :=
  m * m

/-- A concrete residual-code upper model at scale `m`. -/
def conclusion_godel_single_integer_non_quasiisometric_obstruction_residual_length
    (m : Nat) : Nat :=
  m

/-- Divergence of the Gödel length relative to the residual length, in cross-multiplied form. -/
def conclusion_godel_single_integer_non_quasiisometric_obstruction_statement : Prop :=
  ∀ B N : Nat,
    ∃ m : Nat,
      N ≤ m ∧
        B * conclusion_godel_single_integer_non_quasiisometric_obstruction_residual_length m ≤
          conclusion_godel_single_integer_non_quasiisometric_obstruction_godel_length m

/-- Paper label: `thm:conclusion-godel-single-integer-non-quasiisometric-obstruction`. -/
theorem paper_conclusion_godel_single_integer_non_quasiisometric_obstruction :
    conclusion_godel_single_integer_non_quasiisometric_obstruction_statement := by
  intro B N
  refine ⟨max B N, ?_, ?_⟩
  · exact le_max_right B N
  · unfold conclusion_godel_single_integer_non_quasiisometric_obstruction_residual_length
    unfold conclusion_godel_single_integer_non_quasiisometric_obstruction_godel_length
    exact Nat.mul_le_mul_right (max B N) (le_max_left B N)

end Omega.Conclusion
