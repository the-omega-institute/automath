import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-active-fourier-modes-diverge`. -/
theorem paper_conclusion_foldbin_active_fourier_modes_diverge {ι : Type*} [Fintype ι]
    [DecidableEq ι] (zero : ι) (a : ι → ℝ) (Col : ℝ)
    (hCol :
      (Fintype.card ι : ℝ) * (Col - (1 : ℝ) / (Fintype.card ι : ℝ)) =
        ∑ k : { k : ι // k ≠ zero }, (a k) ^ 2)
    (hamp : ∀ k, 0 ≤ a k ∧ a k ≤ 1) :
    (Fintype.card { k : ι // k ≠ zero ∧ a k ≠ 0 } : ℝ) ≥
      (Fintype.card ι : ℝ) * (Col - (1 : ℝ) / (Fintype.card ι : ℝ)) := by
  classical
  rw [hCol]
  let α := { k : ι // k ≠ zero }
  have hsum_le :
      (∑ k : α, (a k) ^ 2) ≤ ∑ k : α, if a k = 0 then (0 : ℝ) else 1 := by
    refine Finset.sum_le_sum ?_
    intro k hk
    by_cases hk0 : a k = 0
    · simp [hk0]
    · have hk_nonneg : 0 ≤ a k := (hamp k).1
      have hk_le_one : a k ≤ 1 := (hamp k).2
      have hsquare : (a k) ^ 2 ≤ 1 := by nlinarith
      simp [hk0, hsquare]
  have hcard_congr :
      Fintype.card { k : ι // k ≠ zero ∧ a k ≠ 0 } =
        Fintype.card { k : α // a k ≠ 0 } := by
    let e : { k : ι // k ≠ zero ∧ a k ≠ 0 } ≃ { k : α // a k ≠ 0 } :=
      { toFun := fun k => ⟨⟨k.1, k.2.1⟩, k.2.2⟩
        invFun := fun k => ⟨k.1.1, ⟨k.1.2, k.2⟩⟩
        left_inv := fun k => Subtype.ext rfl
        right_inv := fun k => Subtype.ext (Subtype.ext rfl) }
    exact Fintype.card_congr e
  have hcard_sum :
      (Fintype.card { k : α // a k ≠ 0 } : ℝ) =
        ∑ k : α, if a k = 0 then (0 : ℝ) else 1 := by
    calc
      (Fintype.card { k : α // a k ≠ 0 } : ℝ) =
          ∑ k : α, if a k ≠ 0 then (1 : ℝ) else 0 := by
        rw [Fintype.card_subtype]
        exact (Finset.sum_boole (fun k : α => a k ≠ 0) Finset.univ).symm
      _ = ∑ k : α, if a k = 0 then (0 : ℝ) else 1 := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        by_cases hk0 : a k = 0 <;> simp [hk0]
  exact calc
    (∑ k : α, (a k) ^ 2) ≤ ∑ k : α, if a k = 0 then (0 : ℝ) else 1 := hsum_le
    _ = (Fintype.card { k : α // a k ≠ 0 } : ℝ) := hcard_sum.symm
    _ = (Fintype.card { k : ι // k ≠ zero ∧ a k ≠ 0 } : ℝ) := by rw [hcard_congr]

end Omega.Conclusion
