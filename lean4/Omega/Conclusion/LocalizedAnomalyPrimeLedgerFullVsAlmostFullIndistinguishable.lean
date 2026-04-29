import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_localized_anomaly_prime_ledger_full_vs_almost_full_indistinguishable_plateau
    (r : Nat) :
    r * (r - 1) / 2 - (r - r) * (r - r - 1) / 2 =
      r * (r - 1) / 2 - (r - (r - 1)) * (r - (r - 1) - 1) / 2 := by
  cases r <;> simp

/-- Paper label:
`cor:conclusion-localized-anomaly-prime-ledger-full-vs-almost-full-indistinguishable`. -/
theorem paper_conclusion_localized_anomaly_prime_ledger_full_vs_almost_full_indistinguishable
    (r : Nat) :
    let multiplicity : Nat -> Nat :=
      fun n => r * (r - 1) / 2 - (r - n) * (r - n - 1) / 2;
    multiplicity r = multiplicity (r - 1) := by
  dsimp
  exact
    conclusion_localized_anomaly_prime_ledger_full_vs_almost_full_indistinguishable_plateau r

end Omega.Conclusion
