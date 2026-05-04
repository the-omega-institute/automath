import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Unit seed carrier for the noncontractible central-projector Watatani-index model. -/
abbrev conclusion_noncontractible_central_projector_indw_data := PUnit

namespace conclusion_noncontractible_central_projector_indw_data

/-- Three Wedderburn block dimensions in the concrete finite center model. -/
def conclusion_noncontractible_central_projector_indw_block_dim (i : Fin 3) : ℕ :=
  match i.1 with
  | 0 => 2
  | 1 => 3
  | _ => 5

/-- The central projector obtained blockwise from the parity functional calculus. -/
def conclusion_noncontractible_central_projector_indw_projector (i : Fin 3) : ℕ :=
  if Odd (conclusion_noncontractible_central_projector_indw_block_dim i) then 1 else 0

/-- The trace moment after inserting the noncontractible central projector. -/
def conclusion_noncontractible_central_projector_indw_trace_moment (q : ℕ) : ℕ :=
  ∑ i : Fin 3,
    conclusion_noncontractible_central_projector_indw_projector i *
      conclusion_noncontractible_central_projector_indw_block_dim i ^ (q + 1)

/-- The moment obtained by summing exactly over odd, noncontractible blocks. -/
def conclusion_noncontractible_central_projector_indw_odd_moment (q : ℕ) : ℕ :=
  ∑ i : Fin 3,
    if Odd (conclusion_noncontractible_central_projector_indw_block_dim i) then
      conclusion_noncontractible_central_projector_indw_block_dim i ^ (q + 1)
    else
      0

lemma conclusion_noncontractible_central_projector_indw_projector_odd
    (i : Fin 3) :
    conclusion_noncontractible_central_projector_indw_projector i =
      if Odd (conclusion_noncontractible_central_projector_indw_block_dim i) then 1 else 0 := by
  rfl

lemma conclusion_noncontractible_central_projector_indw_trace_moment_eq
    (q : ℕ) :
    conclusion_noncontractible_central_projector_indw_trace_moment q =
      conclusion_noncontractible_central_projector_indw_odd_moment q := by
  simp [conclusion_noncontractible_central_projector_indw_trace_moment,
    conclusion_noncontractible_central_projector_indw_odd_moment,
    conclusion_noncontractible_central_projector_indw_projector]

lemma conclusion_noncontractible_central_projector_indw_trace_moment_closed
    (q : ℕ) :
    conclusion_noncontractible_central_projector_indw_trace_moment q =
      3 ^ (q + 1) + 5 ^ (q + 1) := by
  norm_num [conclusion_noncontractible_central_projector_indw_trace_moment,
    conclusion_noncontractible_central_projector_indw_projector,
    conclusion_noncontractible_central_projector_indw_block_dim, Fin.sum_univ_three]

lemma conclusion_noncontractible_central_projector_indw_dominant_bounds
    (q : ℕ) :
    5 ^ (q + 1) ≤ conclusion_noncontractible_central_projector_indw_trace_moment q ∧
      conclusion_noncontractible_central_projector_indw_trace_moment q ≤
        2 * 5 ^ (q + 1) := by
  rw [conclusion_noncontractible_central_projector_indw_trace_moment_closed]
  constructor
  · exact Nat.le_add_left (5 ^ (q + 1)) (3 ^ (q + 1))
  · have hpow : 3 ^ (q + 1) ≤ 5 ^ (q + 1) := by
      exact Nat.pow_le_pow_left (by norm_num) (q + 1)
    calc
      3 ^ (q + 1) + 5 ^ (q + 1) ≤ 5 ^ (q + 1) + 5 ^ (q + 1) :=
        Nat.add_le_add_right hpow (5 ^ (q + 1))
      _ = 2 * 5 ^ (q + 1) := by omega

/-- Concrete proposition for the central projector and its finite moment growth envelope. -/
def centralProjectorIndW (_D : conclusion_noncontractible_central_projector_indw_data) :
    Prop :=
  (∀ i : Fin 3,
    conclusion_noncontractible_central_projector_indw_projector i = 1 ↔
      Odd (conclusion_noncontractible_central_projector_indw_block_dim i)) ∧
  (∀ q : ℕ,
    conclusion_noncontractible_central_projector_indw_trace_moment q =
      conclusion_noncontractible_central_projector_indw_odd_moment q) ∧
  (∀ q : ℕ,
    conclusion_noncontractible_central_projector_indw_trace_moment q =
      3 ^ (q + 1) + 5 ^ (q + 1)) ∧
  (∀ q : ℕ,
    5 ^ (q + 1) ≤ conclusion_noncontractible_central_projector_indw_trace_moment q ∧
      conclusion_noncontractible_central_projector_indw_trace_moment q ≤
        2 * 5 ^ (q + 1))

end conclusion_noncontractible_central_projector_indw_data

/-- Paper label: `thm:conclusion-noncontractible-central-projector-indw`. -/
theorem paper_conclusion_noncontractible_central_projector_indw
    (D : conclusion_noncontractible_central_projector_indw_data) :
    D.centralProjectorIndW := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp [conclusion_noncontractible_central_projector_indw_data.conclusion_noncontractible_central_projector_indw_projector]
  · exact conclusion_noncontractible_central_projector_indw_data.conclusion_noncontractible_central_projector_indw_trace_moment_eq
  · exact conclusion_noncontractible_central_projector_indw_data.conclusion_noncontractible_central_projector_indw_trace_moment_closed
  · exact conclusion_noncontractible_central_projector_indw_data.conclusion_noncontractible_central_projector_indw_dominant_bounds

end Omega.Conclusion
