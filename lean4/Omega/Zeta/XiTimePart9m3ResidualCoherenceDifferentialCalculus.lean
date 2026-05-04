import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped Topology
open scoped BigOperators

lemma xi_time_part9m3_residual_coherence_differential_calculus_term
    (n : ℕ) (T : ℝ) (hT : T ≠ (n : ℝ)) :
    HasDerivAt (fun t : ℝ => (max ((n : ℝ) - t) 0) ^ 2)
      (-2 * max ((n : ℝ) - T) 0) T := by
  by_cases hlt : T < (n : ℝ)
  · have heq :
        (fun t : ℝ => (max ((n : ℝ) - t) 0) ^ 2) =ᶠ[𝓝 T]
          fun t : ℝ => ((n : ℝ) - t) ^ 2 := by
      filter_upwards [eventually_lt_nhds hlt] with t ht
      have hpos : 0 ≤ (n : ℝ) - t := sub_nonneg.mpr ht.le
      simp [max_eq_left hpos]
    have hsub : HasDerivAt (fun t : ℝ => (n : ℝ) - t) (-1) T := by
      simpa using (hasDerivAt_const (x := T) (c := (n : ℝ))).sub (hasDerivAt_id T)
    have hpoly : HasDerivAt (fun t : ℝ => ((n : ℝ) - t) ^ 2)
        (2 * ((n : ℝ) - T) * (-1)) T := by
      convert hsub.mul hsub using 1
      · ext t
        simp [pow_two]
      · ring
    have hmax : max ((n : ℝ) - T) 0 = (n : ℝ) - T := by
      exact max_eq_left (sub_nonneg.mpr hlt.le)
    exact (heq.symm.hasDerivAt_iff.mp hpoly).congr_deriv (by rw [hmax]; ring)
  · have hgt : (n : ℝ) < T := lt_of_le_of_ne (not_lt.mp hlt) hT.symm
    have heq :
        (fun t : ℝ => (max ((n : ℝ) - t) 0) ^ 2) =ᶠ[𝓝 T]
          fun _t : ℝ => 0 := by
      filter_upwards [eventually_gt_nhds hgt] with t ht
      have hnonpos : (n : ℝ) - t ≤ 0 := sub_nonpos.mpr ht.le
      simp [max_eq_right hnonpos]
    have hconst : HasDerivAt (fun _t : ℝ => (0 : ℝ)) 0 T := by
      simpa using (hasDerivAt_const (x := T) (c := (0 : ℝ)))
    have hmax : max ((n : ℝ) - T) 0 = 0 := by
      exact max_eq_right (sub_nonpos.mpr hgt.le)
    exact (heq.symm.hasDerivAt_iff.mp hconst).congr_deriv (by rw [hmax]; ring)

lemma xi_time_part9m3_residual_coherence_differential_calculus_sum
    (d : Multiset ℕ) (T : ℝ) (hT : ∀ n ∈ d, T ≠ (n : ℝ)) :
    HasDerivAt
      (fun t : ℝ => (d.map (fun n : ℕ => (max ((n : ℝ) - t) 0) ^ 2)).sum)
      ((d.map (fun n : ℕ => -2 * max ((n : ℝ) - T) 0)).sum) T := by
  revert hT
  refine Multiset.induction_on d ?nil ?cons
  · simpa using (hasDerivAt_const T (0 : ℝ))
  · intro n s ih hT
    have hn : T ≠ (n : ℝ) := hT n (by simp)
    have hs : ∀ k ∈ s, T ≠ (k : ℝ) := by
      intro k hk
      exact hT k (by simp [hk])
    have hterm :=
      xi_time_part9m3_residual_coherence_differential_calculus_term n T hn
    have hsum := ih hs
    simpa [add_comm, add_left_comm, add_assoc] using hterm.add hsum

lemma xi_time_part9m3_residual_coherence_differential_calculus_sum_smul
    (d : Multiset ℕ) (T : ℝ) :
    (d.map (fun n : ℕ => -2 * max ((n : ℝ) - T) 0)).sum =
      -2 * (d.map (fun n : ℕ => max ((n : ℝ) - T) 0)).sum := by
  refine Multiset.induction_on d ?nil ?cons
  · simp
  · intro n s ih
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih]
    ring

/-- Paper label: `thm:xi-time-part9m3-residual-coherence-differential-calculus`. -/
theorem paper_xi_time_part9m3_residual_coherence_differential_calculus
    (m : ℕ) (d : Multiset ℕ) (T : ℝ) (hT : ∀ n ∈ d, T ≠ (n : ℝ)) :
    HasDerivAt
      (fun t : ℝ =>
        ((2 : ℝ) ^ m)⁻¹ *
          (d.map (fun n : ℕ => (max ((n : ℝ) - t) 0) ^ 2)).sum)
      (-2 * ((2 : ℝ) ^ m)⁻¹ *
        (d.map (fun n : ℕ => max ((n : ℝ) - T) 0)).sum) T := by
  have hsum :=
    xi_time_part9m3_residual_coherence_differential_calculus_sum d T hT
  have hscaled := hsum.const_mul (((2 : ℝ) ^ m)⁻¹)
  refine hscaled.congr_deriv ?_
  rw [xi_time_part9m3_residual_coherence_differential_calculus_sum_smul]
  ring

end Omega.Zeta
