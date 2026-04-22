import Mathlib.Tactic
import Omega.Conclusion.SmithPprimaryRamanujanCutoffCompleteness
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete truncated-audit incompleteness statement: for arbitrarily large cutoffs `E`, the
singleton spectra `[E]` and `[E+1]` agree on every truncated Smith prefix and every truncated
Ramanujan shadow audit up to depth `K`, yet they separate at the first unseen layer `E + 1`. -/
def conclusion_smith_truncated_ramanujan_audit_incompleteness_statement
    (S : Finset ℕ) (K : ℕ) : Prop :=
  ∀ N : ℕ, ∃ E : ℕ, max N K ≤ E ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ K →
      smithPrefixValue (fun _ : Fin 1 => E) k =
        smithPrefixValue (fun _ : Fin 1 => E + 1) k) ∧
    (∀ p ∈ S, ∀ k : ℕ, 1 ≤ k → k ≤ K →
      (p : ℤ) ^ k * (smithPrefixDelta (fun _ : Fin 1 => E) k : ℤ) -
          (p : ℤ) ^ (k - 1) * (smithPrefixDelta (fun _ : Fin 1 => E) (k - 1) : ℤ) =
        (p : ℤ) ^ k * (smithPrefixDelta (fun _ : Fin 1 => E + 1) k : ℤ) -
          (p : ℤ) ^ (k - 1) * (smithPrefixDelta (fun _ : Fin 1 => E + 1) (k - 1) : ℤ)) ∧
    smithPrefixValue (fun _ : Fin 1 => E) (E + 1) + 1 =
      smithPrefixValue (fun _ : Fin 1 => E + 1) (E + 1)

lemma conclusion_smith_truncated_ramanujan_audit_incompleteness_singleton_delta_eq_one
    (E k : ℕ) (hk : k ≤ E) :
    smithPrefixDelta (fun _ : Fin 1 => E) k = 1 := by
  unfold smithPrefixDelta
  simp [hk]

lemma conclusion_smith_truncated_ramanujan_audit_incompleteness_singleton_succ_delta_eq_one
    (E k : ℕ) (hk : k ≤ E) :
    smithPrefixDelta (fun _ : Fin 1 => E + 1) k = 1 := by
  unfold smithPrefixDelta
  simp [le_trans hk (Nat.le_succ E)]

/-- Paper label: `thm:conclusion-smith-truncated-ramanujan-audit-incompleteness`. -/
theorem paper_conclusion_smith_truncated_ramanujan_audit_incompleteness
    (S : Finset ℕ) (K : ℕ) : conclusion_smith_truncated_ramanujan_audit_incompleteness_statement S K := by
  intro N
  refine ⟨max N K, le_rfl, ?_, ?_, ?_⟩
  · have hcutoff :=
      paper_conclusion_smith_pprimary_ramanujan_cutoff_completeness (fun _ : Fin 1 => max N K)
    have htop : smithPrefixTop (fun _ : Fin 1 => max N K) = max N K := by
      simp [smithPrefixTop]
    intro k hk1 hkK
    have hkE : k ≤ max N K := le_trans hkK (le_max_right N K)
    have hkE' : k ≤ smithPrefixTop (fun _ : Fin 1 => max N K) := by
      simpa [htop] using hkE
    simpa [htop] using hcutoff.1 k hk1 hkE'
  · intro p hp k hk1 hkK
    have hkE : k ≤ max N K := le_trans hkK (le_max_right N K)
    have hkm1E : k - 1 ≤ max N K := by omega
    rw [conclusion_smith_truncated_ramanujan_audit_incompleteness_singleton_delta_eq_one
          (E := max N K) (k := k) hkE,
        conclusion_smith_truncated_ramanujan_audit_incompleteness_singleton_delta_eq_one
          (E := max N K) (k := k - 1) hkm1E,
        conclusion_smith_truncated_ramanujan_audit_incompleteness_singleton_succ_delta_eq_one
          (E := max N K) (k := k) hkE,
        conclusion_smith_truncated_ramanujan_audit_incompleteness_singleton_succ_delta_eq_one
          (E := max N K) (k := k - 1) hkm1E]
  · have hcutoff :=
      paper_conclusion_smith_pprimary_ramanujan_cutoff_completeness (fun _ : Fin 1 => max N K)
    have htop : smithPrefixTop (fun _ : Fin 1 => max N K) = max N K := by
      simp [smithPrefixTop]
    simpa [htop] using hcutoff.2.1

end Omega.Conclusion
