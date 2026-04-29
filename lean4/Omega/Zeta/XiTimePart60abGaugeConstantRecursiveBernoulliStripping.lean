import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60ab-gauge-constant-recursive-bernoulli-stripping`. -/
theorem paper_xi_time_part60ab_gauge_constant_recursive_bernoulli_stripping
    (R : Nat) (coeff recovered bernoulli zetaEven : Nat → Nat)
    (h0 : recovered 0 = coeff 0)
    (hstep : ∀ r, r < R → recovered (r + 1) = recovered r + (coeff (r + 1) - coeff r))
    (hmono : ∀ r, r < R → coeff r ≤ coeff (r + 1))
    (hbern : ∀ r, 1 ≤ r → r ≤ R → coeff r = bernoulli (2 * r))
    (hzeta : ∀ r, 1 ≤ r → r ≤ R → zetaEven r = bernoulli (2 * r)) :
    (∀ r, r ≤ R → recovered r = coeff r) ∧
      (∀ r, 1 ≤ r → r ≤ R →
        recovered r = bernoulli (2 * r) ∧ recovered r = zetaEven r) := by
  have hrecover : ∀ r, r ≤ R → recovered r = coeff r := by
    intro r
    induction r with
    | zero =>
        intro _hr
        exact h0
    | succ r ih =>
        intro hr
        have hr_lt : r < R := Nat.lt_of_succ_le hr
        have hr_le : r ≤ R := Nat.le_of_lt hr_lt
        calc
          recovered (Nat.succ r) =
              recovered r + (coeff (r + 1) - coeff r) := by
            simpa [Nat.succ_eq_add_one] using hstep r hr_lt
          _ = coeff r + (coeff (r + 1) - coeff r) := by
            rw [ih hr_le]
          _ = coeff (Nat.succ r) := by
            simpa [Nat.succ_eq_add_one] using Nat.add_sub_of_le (hmono r hr_lt)
  refine ⟨hrecover, ?_⟩
  intro r hr_pos hr_le
  constructor
  · exact (hrecover r hr_le).trans (hbern r hr_pos hr_le)
  · calc
      recovered r = bernoulli (2 * r) := (hrecover r hr_le).trans (hbern r hr_pos hr_le)
      _ = zetaEven r := (hzeta r hr_pos hr_le).symm

end Omega.Zeta
