import Mathlib.Tactic

namespace Omega.Conclusion

/-- Explicit sign-normalized eigenvector model for the cut after the `k`th ordered coordinate. -/
def conclusion_critical_kernel_threshold_nodal_atlas_vector (k : ℕ) (j : ℕ) : ℤ :=
  if j ≤ k then -1 else 1

/-- Positive support of the threshold eigenvector. -/
def conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport
    {n : ℕ} (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => k < j.val

/-- Negative support of the threshold eigenvector. -/
def conclusion_critical_kernel_threshold_nodal_atlas_negativeSupport
    {n : ℕ} (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.val ≤ k

/-- Paper label: `cor:conclusion-critical-kernel-threshold-nodal-atlas`.  In the explicit
interlacing model, the `k`th nontrivial eigenvector has one sign change, two nonempty nodal
domains, threshold support, and the proper threshold cut determines `k` uniquely. -/
theorem paper_conclusion_critical_kernel_threshold_nodal_atlas
    (n k : ℕ) (hk : k + 1 < n) :
    (∀ j : Fin n,
        conclusion_critical_kernel_threshold_nodal_atlas_vector k j.val < 0 ↔ j.val ≤ k) ∧
      (∀ j : Fin n,
        0 < conclusion_critical_kernel_threshold_nodal_atlas_vector k j.val ↔ k < j.val) ∧
      (∃ j : Fin n,
        conclusion_critical_kernel_threshold_nodal_atlas_vector k j.val < 0) ∧
      (∃ j : Fin n,
        0 < conclusion_critical_kernel_threshold_nodal_atlas_vector k j.val) ∧
      (∀ a b : ℕ, a + 1 < n → b + 1 < n →
        conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) a =
          conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) b →
        a = b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.val ≤ k
    · simp [conclusion_critical_kernel_threshold_nodal_atlas_vector, hj]
    · have hkj : k < j.val := by omega
      simp [conclusion_critical_kernel_threshold_nodal_atlas_vector, hj]
  · intro j
    by_cases hj : j.val ≤ k
    · have hnot : ¬k < j.val := by omega
      simp [conclusion_critical_kernel_threshold_nodal_atlas_vector, hj, hnot]
    · have hkj : k < j.val := by omega
      simp [conclusion_critical_kernel_threshold_nodal_atlas_vector, hj, hkj]
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simp [conclusion_critical_kernel_threshold_nodal_atlas_vector]
  · refine ⟨⟨k + 1, hk⟩, ?_⟩
    simp [conclusion_critical_kernel_threshold_nodal_atlas_vector]
  · intro a b ha hb hsupport
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hb_lt_n : b < n := by omega
      let j : Fin n := ⟨b, hb_lt_n⟩
      have hj_a :
          j ∈ conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) a := by
        simp [conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport, j, hab]
      have hj_b :
          j ∉ conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) b := by
        simp [conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport, j]
      have hj_b_mem :
          j ∈ conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) b := by
        simpa [hsupport] using hj_a
      exact hj_b hj_b_mem
    · have ha_lt_n : a < n := by omega
      let j : Fin n := ⟨a, ha_lt_n⟩
      have hj_b :
          j ∈ conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) b := by
        simp [conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport, j, hba]
      have hj_a :
          j ∉ conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) a := by
        simp [conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport, j]
      have hj_a_mem :
          j ∈ conclusion_critical_kernel_threshold_nodal_atlas_positiveSupport (n := n) a := by
        simpa [hsupport] using hj_b
      exact hj_a hj_a_mem

end Omega.Conclusion
