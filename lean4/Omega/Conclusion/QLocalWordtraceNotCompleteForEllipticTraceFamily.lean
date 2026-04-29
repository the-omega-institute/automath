import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Zeta.DynZeta

namespace Omega.Conclusion

open Omega.Zeta

/-- Fixed-`m` local word traces extracted from the softcore golden-mean trace channel. -/
def conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_localTrace
    (m n : ℕ) : ℤ :=
  (Omega.Graph.goldenMeanAdjacency ^ (n + m)).trace

/-- The finite `q`-local packet only records the first `q` shifted traces and forgets the elliptic
host parameter. -/
def conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_qLocalPacket
    (q m : ℕ) (_y : ℚ) : Fin q → ℤ :=
  fun i => conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_localTrace m i.1

/-- A concrete nonconstant rational elliptic host family used to witness loss of the `y`
parameter once only finitely many `q`-local traces are retained. -/
def conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_ellipticHostFamily
    (y : ℚ) : ℚ :=
  (y ^ 2 + y + 1) / (y + 1)

/-- Paper label: `thm:conclusion-q-local-wordtrace-not-complete-for-elliptic-trace-family`.
Fixed-`m` word traces satisfy the same Fibonacci/Lucas recurrence as the golden-mean trace
sequence, every finite `q`-local packet is therefore independent of the elliptic host parameter,
and the explicit rational host family separates two `y`-values with identical local packets. -/
theorem paper_conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family :
    (∀ m n,
      conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_localTrace m (n + 2) =
        conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_localTrace m (n + 1) +
          conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_localTrace m n) ∧
      (∀ q m y₁ y₂,
        conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_qLocalPacket q m y₁ =
          conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_qLocalPacket q m y₂) ∧
      ∃ y₁ y₂ : ℚ,
        y₁ ≠ y₂ ∧
          (∀ q m,
            conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_qLocalPacket q m y₁ =
              conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_qLocalPacket q m y₂) ∧
          conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_ellipticHostFamily y₁ ≠
            conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_ellipticHostFamily y₂ := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n
    simpa [conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_localTrace,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      goldenMean_trace_recurrence_unbounded (n + m)
  · intro q m y₁ y₂
    funext i
    rfl
  · refine ⟨0, 1, by norm_num, ?_, ?_⟩
    · intro q m
      funext i
      rfl
    · have h0 :
        conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_ellipticHostFamily 0 = 1 := by
        norm_num [conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_ellipticHostFamily]
      have h1 :
        conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_ellipticHostFamily 1 =
          (3 / 2 : ℚ) := by
        norm_num [conclusion_q_local_wordtrace_not_complete_for_elliptic_trace_family_ellipticHostFamily]
      rw [h0, h1]
      norm_num

end Omega.Conclusion
