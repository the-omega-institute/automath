import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Omega.Zeta.SmithEntropyInvertsVpInvariants
import Omega.Zeta.XiSmithLossDiscreteCurvatureAtoms

namespace Omega.Conclusion

open Omega.Zeta

/-- The total number of atoms in the Smith partition package. -/
def smithPartitionLength (s : Multiset ℕ) : ℕ :=
  s.card

/-- The total weight of the Smith partition package. -/
def smithPartitionMass (s : Multiset ℕ) : ℕ :=
  s.sum

/-- Concrete formal package for
`thm:conclusion-smith-pkernel-partition-curvature-plateau`. -/
abbrev ConclusionSmithPKernelPartitionCurvaturePlateauStatement : Prop :=
  ∀ s : Multiset ℕ, s ≠ 0 →
    ∃ H : ℕ, H ∈ s ∧
      (∀ v ∈ s, v ≤ H) ∧
      (smithPartitionLength s = s.card ∧ smithPartitionMass s = s.sum) ∧
      (∀ k : ℕ, smithEntropy s (k + 1) - smithEntropy s k = smithDelta s (k + 1)) ∧
      (∀ k : ℕ,
        (s.filter fun v => v = k + 1).card =
          (smithEntropy s (k + 1) - smithEntropy s k) -
            (smithEntropy s (k + 2) - smithEntropy s (k + 1))) ∧
      smithEntropy s (H + 1) = smithEntropy s H ∧
      ∀ k : ℕ, k < H → smithEntropy s k < smithEntropy s (k + 1)

private lemma exists_mem_ge_of_ne_zero (s : Multiset ℕ) (hs : s ≠ 0) :
    ∃ H : ℕ, H ∈ s ∧ ∀ v ∈ s, v ≤ H := by
  induction s using Multiset.induction_on with
  | empty =>
      cases hs rfl
  | @cons a t ih =>
      by_cases ht : t = 0
      · refine ⟨a, by simp, ?_⟩
        intro v hv
        rcases Multiset.mem_cons.mp hv with rfl | hv
        · exact le_rfl
        · simp [ht] at hv
      · rcases ih ht with ⟨H, hHmem, hHmax⟩
        by_cases haH : a ≤ H
        · refine ⟨H, by simp [hHmem], ?_⟩
          intro v hv
          rcases Multiset.mem_cons.mp hv with rfl | hv
          · exact haH
          · exact hHmax v hv
        · have hHa : H ≤ a := by
            exact Nat.le_of_lt (lt_of_not_ge haH)
          refine ⟨a, by simp, ?_⟩
          intro v hv
          rcases Multiset.mem_cons.mp hv with rfl | hv
          · exact le_rfl
          · exact le_trans (hHmax v hv) hHa

/-- `thm:conclusion-smith-pkernel-partition-curvature-plateau` -/
theorem paper_conclusion_smith_p_kernel_partition_curvature_plateau :
    ConclusionSmithPKernelPartitionCurvaturePlateauStatement := by
  intro s hs
  rcases exists_mem_ge_of_ne_zero s hs with ⟨H, hHmem, hHmax⟩
  refine ⟨H, hHmem, hHmax, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · intro k
    rw [smithEntropy_succ_eq_add_delta]
    exact Nat.add_sub_cancel_left (smithEntropy s k) (smithDelta s (k + 1))
  · intro k
    simpa using (paper_xi_smith_loss_discrete_curvature_atoms s).2 k
  · have hHsucc : ∀ v ∈ s, v ≤ H + 1 := by
      intro v hv
      exact le_trans (hHmax v hv) (Nat.le_succ H)
    rw [smithEntropy_eq_sum_of_all_le s (H + 1) hHsucc, smithEntropy_eq_sum_of_all_le s H hHmax]
  · intro k hk
    have hΔpos : 0 < smithDelta s (k + 1) := by
      unfold smithDelta
      have hk' : k + 1 ≤ H := Nat.succ_le_of_lt hk
      have hmem : H ∈ s.filter (fun v => k + 1 ≤ v) := by
        exact Multiset.mem_filter.mpr ⟨hHmem, hk'⟩
      exact Multiset.card_pos_iff_exists_mem.mpr ⟨H, hmem⟩
    rw [smithEntropy_succ_eq_add_delta]
    omega

end Omega.Conclusion
