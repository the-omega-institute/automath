import Mathlib.Tactic
import Omega.Zeta.TwoParamDisjointnessFullSpectrumSecular
import Omega.Zeta.XiTwoParamDisjointnessResultantIntegerFibonacci

namespace Omega.Zeta

/-- Paper-facing resultant and spectrum-disjointness package for the two-parameter model. -/
def xi_two_param_disjointness_spectrum_disjointness_statement : Prop :=
  ∀ (q : ℕ) (b d : ℤ), 2 ≤ q → b ≠ 0 → d ≠ 0 →
    xi_two_param_disjointness_resultant_integer_fibonacci_closedForm q b d ≠ 0 ∧
      xi_two_param_disjointness_full_spectrum_secular_statement q (d : ℝ) (b : ℝ) ∧
      xi_two_param_disjointness_full_spectrum_secular_polynomial q (d : ℝ) (b : ℝ)
          ((d : ℝ) + (q : ℝ) * (b : ℝ)) = 0 ∧
      xi_two_param_disjointness_full_spectrum_secular_polynomial q (d : ℝ) (b : ℝ)
          ((d : ℝ) - (b : ℝ)) = 0 ∧
      (d : ℝ) + (q : ℝ) * (b : ℝ) ≠ (d : ℝ) - (b : ℝ)

/-- Paper label: `cor:xi-two-param-disjointness-spectrum-disjointness`. -/
theorem paper_xi_two_param_disjointness_spectrum_disjointness :
    xi_two_param_disjointness_spectrum_disjointness_statement := by
  intro q b d hq hb hd
  let D : xi_two_param_disjointness_resultant_integer_fibonacci_data :=
    { q := q
      a := 0
      b := b
      d := d
      resultant :=
        xi_two_param_disjointness_resultant_integer_fibonacci_closedForm q b d
      q_ge_two := hq
      b_ne_zero := hb
      d_ne_zero := hd
      resultant_eq_closed := rfl }
  have hResultant := paper_xi_two_param_disjointness_resultant_integer_fibonacci D
  have hSecular := paper_xi_two_param_disjointness_full_spectrum_secular q (d : ℝ) (b : ℝ)
  have hq_ne_zero : q ≠ 0 := by omega
  have hBulkRoot :
      xi_two_param_disjointness_full_spectrum_secular_polynomial q (d : ℝ) (b : ℝ)
          ((d : ℝ) - (b : ℝ)) = 0 := by
    rcases hSecular.2.2.2 with hzero | hroot
    · exact (hq_ne_zero hzero).elim
    · exact hroot
  have hSeparate : (d : ℝ) + (q : ℝ) * (b : ℝ) ≠ (d : ℝ) - (b : ℝ) := by
    intro h
    have hb_real : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hfactor : ((q : ℝ) + 1) * (b : ℝ) = 0 := by
      nlinarith [h]
    have hq_factor : ((q : ℝ) + 1) ≠ 0 := by
      have hpos : 0 < ((q : ℝ) + 1) := by exact_mod_cast Nat.succ_pos q
      exact ne_of_gt hpos
    exact (mul_ne_zero hq_factor hb_real) hfactor
  exact ⟨hResultant.2.1, hSecular, hSecular.2.2.1, hBulkRoot, hSeparate⟩

end Omega.Zeta
