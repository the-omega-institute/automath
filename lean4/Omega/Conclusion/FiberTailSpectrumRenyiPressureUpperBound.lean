import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-fiber-tail-spectrum-renyi-pressure-upper-bound`. -/
theorem paper_conclusion_fiber_tail_spectrum_renyi_pressure_upper_bound {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (q : ℕ) (threshold : ℝ) (hq : 1 ≤ q) (hthreshold : 0 ≤ threshold)
    (hd : ∀ x, 0 ≤ d x) :
    (Fintype.card {x : ι // threshold ≤ d x} : ℝ) * threshold ^ q ≤
      ∑ x : ι, d x ^ q := by
  classical
  have _ : 0 < q := Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  let A : Finset ι := Finset.univ.filter fun x => threshold ≤ d x
  have hcardA : Fintype.card {x : ι // threshold ≤ d x} = A.card := by
    simpa [A] using Fintype.card_subtype (fun x : ι => threshold ≤ d x)
  have hcard :
      (Fintype.card {x : ι // threshold ≤ d x} : ℝ) * threshold ^ q =
        ∑ x ∈ A, threshold ^ q := by
    rw [hcardA]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  calc
    ∑ x ∈ A, threshold ^ q ≤ ∑ x ∈ A, d x ^ q := by
      refine Finset.sum_le_sum ?_
      intro x hx
      have hx_threshold : threshold ≤ d x := by
        simpa [A] using hx
      exact pow_le_pow_left₀ hthreshold hx_threshold q
    _ ≤ ∑ x ∈ (Finset.univ : Finset ι), d x ^ q := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) ?_
      intro x _ _
      exact pow_nonneg (hd x) q
    _ = ∑ x : ι, d x ^ q := by
      simp

end Omega.Conclusion
