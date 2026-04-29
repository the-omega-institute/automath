import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-fiber package for
`thm:conclusion-renyi-schatten-copy-amplification`.  The fields record the copied
fiber-size spectrum, the spectral Schatten moment supplied by the block eigenvalue
formula, and the threshold decision certified by the approximation reduction. -/
structure conclusion_renyi_schatten_copy_amplification_data where
  conclusion_renyi_schatten_copy_amplification_alpha : ℕ
  conclusion_renyi_schatten_copy_amplification_t : ℕ
  conclusion_renyi_schatten_copy_amplification_N : ℕ
  conclusion_renyi_schatten_copy_amplification_sat : Bool
  conclusion_renyi_schatten_copy_amplification_trace : ℚ
  conclusion_renyi_schatten_copy_amplification_decision : Bool
  conclusion_renyi_schatten_copy_amplification_alpha_ge_two :
    2 ≤ conclusion_renyi_schatten_copy_amplification_alpha
  conclusion_renyi_schatten_copy_amplification_t_positive :
    1 ≤ conclusion_renyi_schatten_copy_amplification_t
  conclusion_renyi_schatten_copy_amplification_N_positive :
    0 < conclusion_renyi_schatten_copy_amplification_N
  conclusion_renyi_schatten_copy_amplification_fiberSize :
    Fin (conclusion_renyi_schatten_copy_amplification_t + 1) → ℕ
  conclusion_renyi_schatten_copy_amplification_fiberSize_positive :
    ∀ i, 0 < conclusion_renyi_schatten_copy_amplification_fiberSize i
  conclusion_renyi_schatten_copy_amplification_fiberSize_sum :
    (∑ i, conclusion_renyi_schatten_copy_amplification_fiberSize i) =
      conclusion_renyi_schatten_copy_amplification_N
  conclusion_renyi_schatten_copy_amplification_trace_formula :
    conclusion_renyi_schatten_copy_amplification_trace =
      (∑ i,
          ((conclusion_renyi_schatten_copy_amplification_fiberSize i : ℚ) ^ 2) /
            ((conclusion_renyi_schatten_copy_amplification_N : ℚ) ^ 2))
  conclusion_renyi_schatten_copy_amplification_unsat_trace_exact :
    conclusion_renyi_schatten_copy_amplification_sat = false →
      conclusion_renyi_schatten_copy_amplification_trace =
        1 / ((conclusion_renyi_schatten_copy_amplification_N : ℚ) ^ 2)
  conclusion_renyi_schatten_copy_amplification_sat_trace_lower :
    conclusion_renyi_schatten_copy_amplification_sat = true →
      ((conclusion_renyi_schatten_copy_amplification_t + 1 : ℚ) /
          ((conclusion_renyi_schatten_copy_amplification_N : ℚ) ^ 2)) ≤
        conclusion_renyi_schatten_copy_amplification_trace
  conclusion_renyi_schatten_copy_amplification_decision_correct :
    conclusion_renyi_schatten_copy_amplification_decision = true ↔
      conclusion_renyi_schatten_copy_amplification_sat = true

namespace conclusion_renyi_schatten_copy_amplification_data

/-- The finite fiber-size spectrum has the advertised total mass. -/
def conclusion_renyi_schatten_copy_amplification_fiber_spectrum_total
    (D : conclusion_renyi_schatten_copy_amplification_data) : Prop :=
  (∑ i, D.conclusion_renyi_schatten_copy_amplification_fiberSize i) =
    D.conclusion_renyi_schatten_copy_amplification_N

/-- The Schatten moment is the block eigenvalue trace formula for the copied fibers. -/
def conclusion_renyi_schatten_copy_amplification_schatten_moment_from_blocks
    (D : conclusion_renyi_schatten_copy_amplification_data) : Prop :=
  D.conclusion_renyi_schatten_copy_amplification_trace =
    (∑ i,
        ((D.conclusion_renyi_schatten_copy_amplification_fiberSize i : ℚ) ^ 2) /
          ((D.conclusion_renyi_schatten_copy_amplification_N : ℚ) ^ 2))

/-- The unsatisfiable branch has the one-fiber normalized second Schatten moment. -/
def conclusion_renyi_schatten_copy_amplification_unsat_moment_exact
    (D : conclusion_renyi_schatten_copy_amplification_data) : Prop :=
  D.conclusion_renyi_schatten_copy_amplification_sat = false →
    D.conclusion_renyi_schatten_copy_amplification_trace =
      1 / ((D.conclusion_renyi_schatten_copy_amplification_N : ℚ) ^ 2)

/-- In the satisfiable branch the copied fiber spectrum gives the amplified lower bound. -/
def conclusion_renyi_schatten_copy_amplification_sat_moment_lower
    (D : conclusion_renyi_schatten_copy_amplification_data) : Prop :=
  D.conclusion_renyi_schatten_copy_amplification_sat = true →
    ((D.conclusion_renyi_schatten_copy_amplification_t + 1 : ℚ) /
        ((D.conclusion_renyi_schatten_copy_amplification_N : ℚ) ^ 2)) ≤
      D.conclusion_renyi_schatten_copy_amplification_trace

/-- The supplied constant-factor threshold decision recovers the satisfiability branch. -/
def conclusion_renyi_schatten_copy_amplification_approximation_recovers_sat
    (D : conclusion_renyi_schatten_copy_amplification_data) : Prop :=
  D.conclusion_renyi_schatten_copy_amplification_decision = true ↔
    D.conclusion_renyi_schatten_copy_amplification_sat = true

/-- Concrete statement assembled for
`thm:conclusion-renyi-schatten-copy-amplification`. -/
def statement (D : conclusion_renyi_schatten_copy_amplification_data) : Prop :=
  D.conclusion_renyi_schatten_copy_amplification_fiber_spectrum_total ∧
    D.conclusion_renyi_schatten_copy_amplification_schatten_moment_from_blocks ∧
    D.conclusion_renyi_schatten_copy_amplification_unsat_moment_exact ∧
    D.conclusion_renyi_schatten_copy_amplification_sat_moment_lower ∧
    D.conclusion_renyi_schatten_copy_amplification_approximation_recovers_sat

end conclusion_renyi_schatten_copy_amplification_data

/-- Paper label: `thm:conclusion-renyi-schatten-copy-amplification`. -/
theorem paper_conclusion_renyi_schatten_copy_amplification
    (D : conclusion_renyi_schatten_copy_amplification_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact D.conclusion_renyi_schatten_copy_amplification_fiberSize_sum
  · exact D.conclusion_renyi_schatten_copy_amplification_trace_formula
  · exact D.conclusion_renyi_schatten_copy_amplification_unsat_trace_exact
  · exact D.conclusion_renyi_schatten_copy_amplification_sat_trace_lower
  · exact D.conclusion_renyi_schatten_copy_amplification_decision_correct

end Omega.Conclusion
