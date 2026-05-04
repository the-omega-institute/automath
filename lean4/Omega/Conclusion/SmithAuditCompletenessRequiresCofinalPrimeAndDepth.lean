import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-smith-audit-completeness-requires-cofinal-prime-and-depth`. -/
theorem paper_conclusion_smith_audit_completeness_requires_cofinal_prime_and_depth
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (Delta : ℕ → ℤ)
    (hDelta : ∀ k, Delta k = ∑ i, if k ≤ e i then (1 : ℤ) else 0) :
    ∀ l, Delta l - Delta (l + 1) = ∑ i, if e i = l then (1 : ℤ) else 0 := by
  intro l
  calc
    Delta l - Delta (l + 1) =
        (∑ i, if l ≤ e i then (1 : ℤ) else 0) -
          ∑ i, if l + 1 ≤ e i then (1 : ℤ) else 0 := by
      rw [hDelta l, hDelta (l + 1)]
    _ = ∑ i,
        ((if l ≤ e i then (1 : ℤ) else 0) -
          if l + 1 ≤ e i then (1 : ℤ) else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ i, if e i = l then (1 : ℤ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases hi : e i = l
      · simp [hi]
      · by_cases hle : l ≤ e i
        · have hlt : l < e i := lt_of_le_of_ne hle (fun h => hi h.symm)
          have hsucc : l + 1 ≤ e i := Nat.succ_le_iff.mpr hlt
          simp [hi, hle, hsucc]
        · have hsucc : ¬l + 1 ≤ e i := by
            intro hsucc
            exact hle (Nat.le_trans (Nat.le_succ l) hsucc)
          simp [hi, hle, hsucc]

end Omega.Conclusion
