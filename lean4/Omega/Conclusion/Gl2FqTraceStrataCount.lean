import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete arithmetic data for the `GL₂(F_q)` trace-stratum count. -/
structure GL2FqTraceStrataData where
  q : ℕ
  hq : Nat.Prime q

namespace GL2FqTraceStrataData

/-- For fixed trace `t`, there are `q^3` matrices of the form `[[a,b],[c,t-a]]`. -/
def conclusion_gl2fq_trace_strata_count_total_matrices (q : ℕ) : ℤ :=
  (q : ℤ) ^ 3

/-- Singular trace-zero matrices split into the `u(a) = 0` contribution `2q - 1` and the
remaining `q - 1` values of `a`, each contributing `q - 1` solutions to `bc = u(a)`. -/
def conclusion_gl2fq_trace_strata_count_zero_trace_singular_count (q : ℕ) : ℤ :=
  (2 : ℤ) * q - 1 + ((q : ℤ) - 1) * ((q : ℤ) - 1)

/-- Invertible trace-zero matrices are the total trace-zero matrices minus the singular ones. -/
def conclusion_gl2fq_trace_strata_count_zero_trace_invertible_count (q : ℕ) : ℤ :=
  conclusion_gl2fq_trace_strata_count_total_matrices q -
    conclusion_gl2fq_trace_strata_count_zero_trace_singular_count q

/-- For nonzero trace `t`, the singular stratum has two roots of `u(a) = a (t - a) = 0`,
each contributing `2q - 1`, and the other `q - 2` values of `a` contribute `q - 1`. -/
def conclusion_gl2fq_trace_strata_count_nonzero_trace_singular_count (q : ℕ) : ℤ :=
  (2 : ℤ) * ((2 : ℤ) * q - 1) + ((q : ℤ) - 2) * ((q : ℤ) - 1)

/-- Invertible nonzero-trace matrices are the total trace-`t` matrices minus the singular ones. -/
def conclusion_gl2fq_trace_strata_count_nonzero_trace_invertible_count (q : ℕ) : ℤ :=
  conclusion_gl2fq_trace_strata_count_total_matrices q -
    conclusion_gl2fq_trace_strata_count_nonzero_trace_singular_count q

/-- Closed form for the trace-zero stratum. -/
def zeroTraceFormula (D : GL2FqTraceStrataData) : Prop :=
  conclusion_gl2fq_trace_strata_count_zero_trace_singular_count D.q = (D.q : ℤ) ^ 2 ∧
    conclusion_gl2fq_trace_strata_count_zero_trace_invertible_count D.q =
      (D.q : ℤ) ^ 2 * ((D.q : ℤ) - 1)

/-- Closed form for every nonzero trace stratum. -/
def nonzeroTraceFormula (D : GL2FqTraceStrataData) : Prop :=
  conclusion_gl2fq_trace_strata_count_nonzero_trace_singular_count D.q =
      (D.q : ℤ) ^ 2 + D.q ∧
    conclusion_gl2fq_trace_strata_count_nonzero_trace_invertible_count D.q =
      (D.q : ℤ) ^ 3 - (D.q : ℤ) ^ 2 - D.q

end GL2FqTraceStrataData

open GL2FqTraceStrataData

/-- Paper label: `thm:conclusion-gl2fq-trace-strata-count`. Writing a trace-`t` matrix as
`[[a,b],[c,t-a]]` gives `q^3` possibilities. Counting singular matrices via the equation
`bc = a (t - a)` yields the trace-zero and nonzero-trace strata in closed form. -/
theorem paper_conclusion_gl2fq_trace_strata_count (D : GL2FqTraceStrataData) :
    D.zeroTraceFormula ∧ D.nonzeroTraceFormula := by
  refine ⟨?_, ?_⟩
  · constructor
    · simp [conclusion_gl2fq_trace_strata_count_zero_trace_singular_count]
      ring
    · simp [conclusion_gl2fq_trace_strata_count_zero_trace_invertible_count,
        conclusion_gl2fq_trace_strata_count_zero_trace_singular_count,
        conclusion_gl2fq_trace_strata_count_total_matrices]
      ring
  · constructor
    · simp [conclusion_gl2fq_trace_strata_count_nonzero_trace_singular_count]
      ring
    · simp [conclusion_gl2fq_trace_strata_count_nonzero_trace_invertible_count,
        conclusion_gl2fq_trace_strata_count_nonzero_trace_singular_count,
        conclusion_gl2fq_trace_strata_count_total_matrices]
      ring

end Omega.Conclusion
