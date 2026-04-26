import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Folding.FoldEndpointMmMinusOneUnique

private theorem fold_endpoint_mm_minus_one_unique_even_add_two (n : ℕ) :
    Even (n + 2) ↔ Even n := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩

private theorem fold_endpoint_mm_minus_one_unique_fib_step (m : ℕ) :
    Nat.fib (m + 4) - 1 = (Nat.fib (m + 2) - 1) + Nat.fib (m + 3) := by
  have hfib : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.fib_add_two (n := m + 2))
  have hpos : 0 < Nat.fib (m + 2) := Omega.fib_succ_pos (m + 1)
  omega

private theorem fold_endpoint_mm_minus_one_unique_alternating_sum (m : ℕ) :
    (∑ k : Fin m,
        (if Even (m - (k.1 + 1)) then 1 else 0) * Nat.fib (k.1 + 2)) =
      Nat.fib (m + 2) - 1 := by
  induction m using Nat.twoStepInduction with
  | zero =>
      simp
  | one =>
      norm_num [Nat.fib]
  | more m ih =>
      rw [Fin.sum_univ_castSucc (n := m + 1)]
      rw [Fin.sum_univ_castSucc (n := m)]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hsum :
          (∑ k : Fin m,
              (if Even (m + 2 - (k.1 + 1)) then 1 else 0) * Nat.fib (k.1 + 2)) =
            ∑ k : Fin m,
              (if Even (m - (k.1 + 1)) then 1 else 0) * Nat.fib (k.1 + 2) := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        have hsub : m + 2 - (k.1 + 1) = (m - (k.1 + 1)) + 2 := by
          have hklt := k.2
          omega
        have hev : Even (m + 2 - (k.1 + 1)) ↔ Even (m - (k.1 + 1)) := by
          rw [hsub]
          exact fold_endpoint_mm_minus_one_unique_even_add_two _
        by_cases h : Even (m - (k.1 + 1))
        · rw [if_pos (hev.mpr h), if_pos h]
        · have hnot : ¬ Even (m + 2 - (k.1 + 1)) := fun h' => h (hev.mp h')
          rw [if_neg hnot, if_neg h]
      rw [hsum, ih]
      have hmid : ¬ Even (m + 2 - (m + 1)) := by
        intro h
        rcases h with ⟨k, hk⟩
        omega
      have hlast : Even (m + 2 - (m + 2)) := by
        exact ⟨0, by omega⟩
      rw [if_neg hmid, if_pos hlast]
      simp [fold_endpoint_mm_minus_one_unique_fib_step]

/-- The alternating endpoint witness for `F_{m+2} - 1`, with uniqueness. -/
theorem paper_fold_endpoint_mm_minus_one_unique (m : ℕ) (hm : 2 ≤ m) :
    ∃! ω : Fin m → ℕ,
      (∀ k, ω k = 0 ∨ ω k = 1) ∧
        (∑ k : Fin m, ω k * Nat.fib (k.1 + 2)) = Nat.fib (m + 2) - 1 ∧
          ∀ k : Fin m, ω k = (if Even (m - (k.1 + 1)) then 1 else 0) := by
  have fold_endpoint_mm_minus_one_unique_m_ge_two : 2 ≤ m := hm
  let witness : Fin m → ℕ := fun k => if Even (m - (k.1 + 1)) then 1 else 0
  refine ⟨witness, ?_, ?_⟩
  · constructor
    · intro k
      by_cases h : Even (m - (k.1 + 1)) <;> simp [witness, h]
    · constructor
      · simpa [witness] using fold_endpoint_mm_minus_one_unique_alternating_sum m
      · intro k
        have _ : 2 ≤ m := fold_endpoint_mm_minus_one_unique_m_ge_two
        rfl
  · intro ω hω
    funext k
    exact hω.2.2 k

end Omega.Folding.FoldEndpointMmMinusOneUnique
