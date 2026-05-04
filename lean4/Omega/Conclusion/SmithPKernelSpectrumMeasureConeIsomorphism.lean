import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

private lemma conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_min_step
    (k l : ℕ) (hk : 1 ≤ k) :
    min k l - min (k - 1) l = if k ≤ l then 1 else 0 := by
  by_cases hkl : k ≤ l
  · have hprev : k - 1 ≤ l := le_trans (Nat.sub_le k 1) hkl
    rw [min_eq_left hkl, min_eq_left hprev, if_pos hkl]
    omega
  · have hlt : l < k := lt_of_not_ge hkl
    have hleprev : l ≤ k - 1 := by omega
    rw [min_eq_right (Nat.le_of_lt hlt), min_eq_right hleprev, if_neg hkl]
    simp

private lemma conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_term_step
    (μ : ℕ → ℕ) (k l : ℕ) (hk : 1 ≤ k) :
    μ l * min k l - μ l * min (k - 1) l = if k ≤ l then μ l else 0 := by
  rw [← mul_tsub]
  rw [conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_min_step k l hk]
  by_cases hkl : k ≤ l <;> simp [hkl]

private lemma conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_tail_identity
    (s : Finset ℕ) (μ : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) :
    (∑ l ∈ s, μ l * min k l) - (∑ l ∈ s, μ l * min (k - 1) l) =
      ∑ l ∈ s.filter (fun l => k ≤ l), μ l := by
  classical
  have hle :
      ∀ l ∈ s, μ l * min (k - 1) l ≤ μ l * min k l := by
    intro l _
    exact Nat.mul_le_mul_left (μ l) (min_le_min_right l (Nat.sub_le k 1))
  calc
    (∑ l ∈ s, μ l * min k l) - (∑ l ∈ s, μ l * min (k - 1) l)
        = ∑ l ∈ s, (μ l * min k l - μ l * min (k - 1) l) := by
            simpa using
              (Finset.sum_tsub_distrib
                (s := s)
                (f := fun l => μ l * min k l)
                (g := fun l => μ l * min (k - 1) l)
                hle).symm
    _ = ∑ l ∈ s, if k ≤ l then μ l else 0 := by
          refine Finset.sum_congr rfl ?_
          intro l _
          exact conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_term_step μ k l hk
    _ = ∑ l ∈ s.filter (fun l => k ≤ l), μ l := by
          rw [Finset.sum_filter]

private lemma conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_tail_succ
    (s : Finset ℕ) (μ : ℕ → ℕ) {l : ℕ} (hl : l ∈ s) :
    (∑ x ∈ s.filter (fun x => l ≤ x), μ x) =
      μ l + ∑ x ∈ s.filter (fun x => l + 1 ≤ x), μ x := by
  classical
  have hfilter :
      s.filter (fun x => l ≤ x) = insert l (s.filter fun x => l + 1 ≤ x) := by
    ext x
    by_cases hxl : x = l
    · subst x
      simp [hl]
    · simp [hxl]
      intro _hx
      omega
  rw [hfilter, Finset.sum_insert]
  · simp

private lemma conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_coeff_eq_tail_sub
    (s : Finset ℕ) (μ : ℕ → ℕ) {l : ℕ} (hl : l ∈ s) :
    μ l =
      (∑ x ∈ s.filter (fun x => l ≤ x), μ x) -
        ∑ x ∈ s.filter (fun x => l + 1 ≤ x), μ x := by
  rw [conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_tail_succ s μ hl]
  exact (Nat.add_sub_cancel_right (μ l) _).symm

/-- Paper label:
`thm:conclusion-smith-p-kernel-spectrum-measure-cone-isomorphism`. -/
theorem paper_conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism
    (s : Finset ℕ) (μ ν : ℕ → ℕ) (hs : ∀ l ∈ s, 1 ≤ l)
    (heq : ∀ k, (∑ l ∈ s, μ l * min k l) = ∑ l ∈ s, ν l * min k l) :
    (∀ l ∈ s, μ l = ν l) ∧
      (∀ k, 1 ≤ k →
        (∑ l ∈ s, μ l * min k l) - (∑ l ∈ s, μ l * min (k - 1) l) =
          ∑ l ∈ s.filter (fun l => k ≤ l), μ l) := by
  classical
  have htail_eq :
      ∀ k, 1 ≤ k →
        (∑ l ∈ s.filter (fun l => k ≤ l), μ l) =
          ∑ l ∈ s.filter (fun l => k ≤ l), ν l := by
    intro k hk
    rw [← conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_tail_identity s μ k hk,
      ← conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_tail_identity s ν k hk,
      heq k, heq (k - 1)]
  refine ⟨?_, conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_tail_identity s μ⟩
  intro l hl
  calc
    μ l =
        (∑ x ∈ s.filter (fun x => l ≤ x), μ x) -
          ∑ x ∈ s.filter (fun x => l + 1 ≤ x), μ x :=
        conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_coeff_eq_tail_sub s μ hl
    _ =
        (∑ x ∈ s.filter (fun x => l ≤ x), ν x) -
          ∑ x ∈ s.filter (fun x => l + 1 ≤ x), ν x := by
        rw [htail_eq l (hs l hl), htail_eq (l + 1) (Nat.succ_pos l)]
    _ = ν l :=
        (conclusion_smith_p_kernel_spectrum_measure_cone_isomorphism_coeff_eq_tail_sub s ν hl).symm

end Omega.Conclusion
