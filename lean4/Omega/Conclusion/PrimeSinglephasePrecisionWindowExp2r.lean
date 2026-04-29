import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite-box packing lower estimate for the single-phase prime window. -/
def conclusion_prime_singlephase_precision_window_exp2r_lower (r A : Nat) : Nat :=
  (2 * A + 1) ^ r

/-- The algebraic norm-separation upper estimate; the factor `2 ^ r - 1` is the certified
multi-square-root degree loss. -/
def conclusion_prime_singlephase_precision_window_exp2r_upper (r A p_r : Nat) : Nat :=
  1 + (2 ^ r - 1) * (3 * A * r * p_r)

/-- Dyadic precision lies in the certified finite-box window, and the two estimates are compatible. -/
def conclusion_prime_singlephase_precision_window_exp2r_window
    (r A p_r B : Nat) : Prop :=
  conclusion_prime_singlephase_precision_window_exp2r_lower r A ≤ B ∧
    B ≤ conclusion_prime_singlephase_precision_window_exp2r_upper r A p_r ∧
    conclusion_prime_singlephase_precision_window_exp2r_lower r A ≤
      conclusion_prime_singlephase_precision_window_exp2r_upper r A p_r

/-- Paper label: `cor:conclusion-prime-singlephase-precision-window-exp2r`. -/
theorem paper_conclusion_prime_singlephase_precision_window_exp2r
    (r A p_r B : Nat)
    (h_packing :
      conclusion_prime_singlephase_precision_window_exp2r_lower r A ≤ B)
    (h_separation :
      B ≤ conclusion_prime_singlephase_precision_window_exp2r_upper r A p_r) :
    conclusion_prime_singlephase_precision_window_exp2r_window r A p_r B := by
  exact ⟨h_packing, h_separation, le_trans h_packing h_separation⟩

end Omega.Conclusion
