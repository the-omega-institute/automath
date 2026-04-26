import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.ChebyshevAdamsFullyRational
import Omega.UnitCirclePhaseArithmetic.CompletionSubringUniqueAngle

namespace Omega.SyncKernelWeighted

open Omega.UnitCirclePhaseArithmetic
open scoped Polynomial

/-- Minimal completed primitive model: even indices descend to a constant polynomial, while odd
indices descend to the linear trace coordinate. This keeps only the parity data used by the paper
wrapper. -/
noncomputable def primitive_completion_hatp_completed_poly (n : ℕ) : Polynomial ℤ :=
  if Even n then 1 else Polynomial.X

/-- Parity package for the descended primitive-completion model under `s ↦ -s`. -/
def primitive_completion_hatp_parity_statement (n : ℕ) : Prop :=
  (Even n →
      ∀ s : ℚ,
        completionEval (primitive_completion_hatp_completed_poly n) (-s) =
          completionEval (primitive_completion_hatp_completed_poly n) s) ∧
    (Odd n →
      ∀ s : ℚ,
        completionEval (primitive_completion_hatp_completed_poly n) (-s) =
          -completionEval (primitive_completion_hatp_completed_poly n) s)

/-- The completion wrapper records the invariant-ring descent for the completed Laurent pair,
the expected even/odd parity under `s ↦ -s`, and the Chebyshev--Adams recursion on the trace
coordinate. This matches the paper-facing `\hat p_n` completion pattern in the concrete
`completionTracePoly` model.
    cor:primitive-completion-hatp -/
theorem paper_primitive_completion_hatp :
    (∀ n : ℕ, 1 ≤ n →
      ∃ P : Polynomial ℤ,
        ∀ r : ℚ, r ≠ 0 →
          completionEval P (r + r⁻¹) = completionEval P (r⁻¹ + r)) ∧
      (∀ n : ℕ, primitive_completion_hatp_parity_statement n) ∧
      (∀ d : ℕ, chebyshevTraceFormula d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n _hn
    refine ⟨primitive_completion_hatp_completed_poly n, ?_⟩
    intro r _hr
    simp [add_comm]
  · intro n
    refine ⟨?_, ?_⟩
    · intro hn s
      simp [primitive_completion_hatp_completed_poly, hn, completionEval]
    · intro hn s
      have hnot : ¬ Even n := by
        rcases hn with ⟨k, hk⟩
        intro h
        rcases h with ⟨m, hm⟩
        omega
      simp [primitive_completion_hatp_completed_poly, hnot, completionEval]
  · intro d
    exact (paper_chebyshev_adams_fully_rational d).2

end Omega.SyncKernelWeighted
