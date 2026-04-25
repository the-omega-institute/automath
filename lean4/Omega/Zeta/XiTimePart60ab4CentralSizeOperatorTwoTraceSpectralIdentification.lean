import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part60ab4-central-size-operator-two-trace-spectral-identification`.
The weighted trace is unchanged when both the numerator and denominator are first normalized by
the finite output cardinality. -/
theorem paper_xi_time_part60ab4_central_size_operator_two_trace_spectral_identification
    {ι : Type} [Fintype ι] (d : ι → ℝ) (f : ℝ → ℝ)
    (hden : (∑ i, d i) ≠ 0) :
    (∑ i, d i * f (d i)) / (∑ i, d i) =
      ((∑ i, d i * f (d i)) / Fintype.card ι) / ((∑ i, d i) / Fintype.card ι) := by
  classical
  have hcard_nat : Fintype.card ι ≠ 0 := by
    intro hcard
    have hι : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    haveI := hι
    simp at hden
  have hcard_real : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  field_simp [hden, hcard_real]

end Omega.Zeta
