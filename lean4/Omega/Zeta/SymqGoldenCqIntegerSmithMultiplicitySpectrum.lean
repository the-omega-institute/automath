import Mathlib.Tactic

namespace Omega.Zeta

/-- Multiplicity of the Smith exponent `k` for the integer restriction of the golden
`q`-th symmetric block model.  It is the closed-form count obtained from the one
unit exponent and the block exponents `(⌊r/2⌋, ⌈r/2⌉)` for `0 ≤ r ≤ q`. -/
def xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (q k : ℕ) : ℕ :=
  if k = 0 then 3
  else if 2 * k < q then 4
  else if 2 * k = q then 3
  else if 2 * k = q + 1 then 1
  else 0

/-- Paper label: `cor:xi-symq-golden-cq-integer-smith-multiplicity-spectrum`. -/
theorem paper_xi_symq_golden_cq_integer_smith_multiplicity_spectrum (m : ℕ) (hm : 1 ≤ m) :
    xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m) 0 = 3 ∧
      (∀ k : ℕ, 1 ≤ k → k < m →
        xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m) k = 4) ∧
      xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m) m = 3 ∧
      xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m + 1) 0 = 3 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ m →
        xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m + 1) k = 4) ∧
      xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m + 1) (m + 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult]
  · intro k hk_pos hk_lt
    have hk_ne_zero : k ≠ 0 := by omega
    have hlt : 2 * k < 2 * m := by omega
    simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult, hk_ne_zero, hlt]
  · have hm_ne_zero : m ≠ 0 := by omega
    simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult, hm_ne_zero]
  · simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult]
  · intro k hk_pos hk_le
    have hk_ne_zero : k ≠ 0 := by omega
    have hlt : 2 * k < 2 * m + 1 := by omega
    simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult, hk_ne_zero, hlt]
  · have heq : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult, heq]

end Omega.Zeta
