import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The hockey-stick sum with the two omitted low-order terms restored. -/
theorem conclusion_finite_moment_order_phase_diagram_single_certificate_compilation_sum_add_eleven
    (Q : ℕ) (hQ : 3 ≤ Q) :
    (∑ q ∈ Finset.Icc 2 Q, Nat.choose (q + 9) 9) + 11 = Nat.choose (Q + 10) 10 := by
  induction Q, hQ using Nat.le_induction with
  | base =>
      native_decide
  | succ Q hQ ih =>
      rw [Finset.sum_Icc_succ_top (a := 2) (b := Q) (by omega)]
      have hterm : (Q + 1 + 9).choose 9 = (Q + 10).choose 9 := by
        have h : Q + 1 + 9 = Q + 10 := by omega
        rw [h]
      have htop : (Q + 1 + 10).choose 10 = (Q + 11).choose 10 := by
        have h : Q + 1 + 10 = Q + 11 := by omega
        rw [h]
      rw [hterm, htop]
      have hchoose :
          (Q + 11).choose 10 = (Q + 10).choose 9 + (Q + 10).choose 10 := by
        simpa using Nat.choose_succ_succ' (Q + 10) 9
      calc
        (∑ k ∈ Finset.Icc 2 Q, (k + 9).choose 9) + (Q + 10).choose 9 + 11
            = ((∑ k ∈ Finset.Icc 2 Q, (k + 9).choose 9) + 11) +
                (Q + 10).choose 9 := by
              omega
        _ = (Q + 10).choose 10 + (Q + 10).choose 9 := by
              rw [ih]
        _ = (Q + 10).choose 9 + (Q + 10).choose 10 := by omega
        _ = (Q + 11).choose 10 := hchoose.symm

/-- Paper label:
`thm:conclusion-finite-moment-order-phase-diagram-single-certificate-compilation`. -/
theorem paper_conclusion_finite_moment_order_phase_diagram_single_certificate_compilation
    (Q : ℕ) (hQ : 3 ≤ Q) :
    (∑ q ∈ Finset.Icc 2 Q, Nat.choose (q + 9) 9) = Nat.choose (Q + 10) 10 - 11 := by
  have hsum :=
    conclusion_finite_moment_order_phase_diagram_single_certificate_compilation_sum_add_eleven
      Q hQ
  omega

end Omega.Conclusion
