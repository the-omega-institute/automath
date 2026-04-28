import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-canonical-fixedpoint-primitive-sharp-error-primepower`. -/
theorem paper_conclusion_canonical_fixedpoint_primitive_sharp_error_primepower
    (base : ℕ) (Pi N tau : ℕ → ℕ) (hbase : 2 ≤ base)
    (herror : ∀ k, 1 ≤ k → Pi k ≤ base ^ k ∧
      base ^ k - Pi k ≤ (tau k - 1) * base ^ (k / 2))
    (hprime : ∀ p ell, Nat.Prime p → 1 ≤ ell →
      Pi (p ^ ell) = base ^ (p ^ ell) - base ^ (p ^ (ell - 1)))
    (hN : ∀ k, 1 ≤ k → k * N k = Pi k) :
    (∀ k, 1 ≤ k → Pi k ≤ base ^ k ∧
      base ^ k - Pi k ≤ (tau k - 1) * base ^ (k / 2)) ∧
      (∀ p ell, Nat.Prime p → 1 ≤ ell →
        Pi (p ^ ell) = base ^ (p ^ ell) - base ^ (p ^ (ell - 1)) ∧
          p ^ ell * N (p ^ ell) = Pi (p ^ ell)) := by
  have _ : 2 ≤ base := hbase
  refine ⟨herror, ?_⟩
  intro p ell hp hell
  refine ⟨hprime p ell hp hell, ?_⟩
  exact hN (p ^ ell) (Nat.succ_le_of_lt (pow_pos hp.pos ell))

end Omega.Conclusion
