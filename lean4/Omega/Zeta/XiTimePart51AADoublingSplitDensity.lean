import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part51aa-doubling-split-density`. -/
theorem paper_xi_time_part51aa_doubling_split_density :
    (∀ N : ℕ, ((Finset.range (3 * N)).filter (fun m => ¬ 3 ∣ m + 2)).card = 2 * N) ∧
      (∀ N : ℕ, ((Finset.range (3 * N)).filter (fun m => 3 ∣ m + 2)).card = N) := by
  constructor
  · intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [← Nat.count_eq_card_filter_range] at ih ⊢
        rw [show 3 * (N + 1) = 3 * N + 3 by omega, Nat.count_add]
        have hblock : Nat.count (fun k => ¬ 3 ∣ (3 * N + k) + 2) 3 = 2 := by
          have hp0 : ¬ 3 ∣ (3 * N + 0) + 2 := by
            intro h
            omega
          have hp1 : 3 ∣ (3 * N + 1) + 2 := by
            exact ⟨N + 1, by ring⟩
          have hp2 : ¬ 3 ∣ (3 * N + 2) + 2 := by
            intro h
            omega
          rw [show 3 = 2 + 1 by norm_num, Nat.count_succ]
          rw [show 2 = 1 + 1 by norm_num, Nat.count_succ]
          rw [show 1 = 0 + 1 by norm_num, Nat.count_succ]
          simp [hp0, hp1, hp2]
        rw [ih, hblock]
        omega
  · intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [← Nat.count_eq_card_filter_range] at ih ⊢
        rw [show 3 * (N + 1) = 3 * N + 3 by omega, Nat.count_add]
        have hblock : Nat.count (fun k => 3 ∣ (3 * N + k) + 2) 3 = 1 := by
          have hp0 : ¬ 3 ∣ (3 * N + 0) + 2 := by
            intro h
            omega
          have hp1 : 3 ∣ (3 * N + 1) + 2 := by
            exact ⟨N + 1, by ring⟩
          have hp2 : ¬ 3 ∣ (3 * N + 2) + 2 := by
            intro h
            omega
          rw [show 3 = 2 + 1 by norm_num, Nat.count_succ]
          rw [show 2 = 1 + 1 by norm_num, Nat.count_succ]
          rw [show 1 = 0 + 1 by norm_num, Nat.count_succ]
          simp [hp0, hp1, hp2]
        rw [ih, hblock]

end Omega.Zeta
