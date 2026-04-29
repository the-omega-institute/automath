import Mathlib.Tactic

namespace Omega.Zeta

/-- The visible `p`-primary depth of the Fibonacci modulus `F_{m+2}`. -/
def xi_fold_congruence_pprimary_quotient_depth_nu (m p : ℕ) : ℕ :=
  (Nat.fib (m + 2)).factorization p

/-- Existence of the finite `p^s` quotient, expressed as divisibility of the modulus. -/
def xi_fold_congruence_pprimary_quotient_depth_exists_quotient (m p s : ℕ) : Prop :=
  p ^ s ∣ Nat.fib (m + 2)

/-- Paper label: `thm:xi-fold-congruence-pprimary-quotient-depth`. -/
theorem paper_xi_fold_congruence_pprimary_quotient_depth
    (m p s : ℕ) (hp : Nat.Prime p) (hs : 1 ≤ s) :
    xi_fold_congruence_pprimary_quotient_depth_exists_quotient m p s ↔
      s ≤ xi_fold_congruence_pprimary_quotient_depth_nu m p := by
  have _ : 1 ≤ s := hs
  have hfib : Nat.fib (m + 2) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.fib_pos.2 (by omega))
  simpa [xi_fold_congruence_pprimary_quotient_depth_exists_quotient,
    xi_fold_congruence_pprimary_quotient_depth_nu] using
      (hp.pow_dvd_iff_le_factorization (k := s) hfib)

end Omega.Zeta
