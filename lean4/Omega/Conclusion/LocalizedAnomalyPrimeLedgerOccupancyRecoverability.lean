import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_pair_count_le
    {a b : Nat} (h : a <= b) : a * (a - 1) / 2 <= b * (b - 1) / 2 := by
  simpa [Nat.choose_two_right] using Nat.choose_le_choose 2 h

lemma conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_pair_count_step
    {a : Nat} (ha : 1 <= a) :
    a * (a - 1) / 2 - (a - 1) * (a - 1 - 1) / 2 = a - 1 := by
  rw [← Nat.choose_two_right a, ← Nat.choose_two_right (a - 1)]
  cases a with
  | zero =>
      omega
  | succ a =>
      simp [Nat.choose_succ_succ]

lemma conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_multiplicity_step
    {r n : Nat} (hn : n + 1 <= r - 1) :
    r * (r - 1) / 2 - (r - n) * (r - n - 1) / 2 + (r - n - 1) =
      r * (r - 1) / 2 - (r - (n + 1)) * (r - (n + 1) - 1) / 2 := by
  have hn_le_r : n <= r := by omega
  have hsucc_le_r : n + 1 <= r := by omega
  have hpos : 1 <= r - n := by omega
  have hsub : r - (n + 1) = r - n - 1 := by omega
  have hpair_le :
      (r - n) * (r - n - 1) / 2 <= r * (r - 1) / 2 :=
    conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_pair_count_le
      (by omega : r - n <= r)
  have hdiff :
      (r - n) * (r - n - 1) / 2 -
          (r - n - 1) * (r - n - 1 - 1) / 2 =
        r - n - 1 :=
    conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_pair_count_step hpos
  rw [hsub]
  omega

lemma conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_strict_step
    {r n : Nat} (hn : n + 1 <= r - 1) :
    r * (r - 1) / 2 - (r - n) * (r - n - 1) / 2 <
      r * (r - 1) / 2 - (r - (n + 1)) * (r - (n + 1) - 1) / 2 := by
  have hstep :=
    conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_multiplicity_step
      (r := r) (n := n) hn
  have hpositive : 0 < r - n - 1 := by omega
  omega

lemma conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_plateau (r : Nat) :
    r * (r - 1) / 2 - (r - (r - 1)) * (r - (r - 1) - 1) / 2 =
      r * (r - 1) / 2 - (r - r) * (r - r - 1) / 2 := by
  cases r <;> simp

/-- Paper label:
`thm:conclusion-localized-anomaly-prime-ledger-occupancy-recoverability`. -/
theorem paper_conclusion_localized_anomaly_prime_ledger_occupancy_recoverability (r : Nat)
    (hr : 2 <= r) :
    let f : Nat -> Nat :=
      fun n => r * (r - 1) / 2 - (r - n) * (r - n - 1) / 2;
    (∀ n : Nat, n + 1 <= r - 1 -> f n < f (n + 1)) ∧ f (r - 1) = f r ∧
      ∀ n m : Nat, n <= r - 1 -> m <= r - 1 -> f n = f m -> n = m := by
  dsimp
  constructor
  · intro n hn
    exact
      conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_strict_step
        (r := r) (n := n) hn
  constructor
  · exact conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_plateau r
  · intro n m hn hm hnm
    by_contra hne
    wlog hlt : n < m generalizing n m with H
    · have hmn : m < n := by omega
      exact H m n hm hn hnm.symm (by omega) hmn
    have hsucc_le : n + 1 <= r - 1 := by omega
    have hle : n + 1 <= m := by omega
    have hfirst :
        r * (r - 1) / 2 - (r - n) * (r - n - 1) / 2 <
          r * (r - 1) / 2 - (r - (n + 1)) * (r - (n + 1) - 1) / 2 :=
      conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_strict_step
        (r := r) (n := n) hsucc_le
    have hmono :
        r * (r - 1) / 2 - (r - (n + 1)) * (r - (n + 1) - 1) / 2 <=
          r * (r - 1) / 2 - (r - m) * (r - m - 1) / 2 := by
      have hpair_le :
          (r - m) * (r - m - 1) / 2 <=
            (r - (n + 1)) * (r - (n + 1) - 1) / 2 :=
        conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_pair_count_le
          (by omega : r - m <= r - (n + 1))
      have hupper :
          (r - (n + 1)) * (r - (n + 1) - 1) / 2 <= r * (r - 1) / 2 :=
        conclusion_localized_anomaly_prime_ledger_occupancy_recoverability_pair_count_le
          (by omega : r - (n + 1) <= r)
      omega
    omega

end Omega.Conclusion
