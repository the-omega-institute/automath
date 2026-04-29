import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9fa-exact-screen-minimal-size-matroid-basis`. -/
theorem paper_xi_time_part9fa_exact_screen_minimal_size_matroid_basis {V : Type*}
    [DecidableEq V] (m n : ℕ) (r : Finset V → ℕ) (hzero : r ∅ = 0)
    (hrho : ∀ S, r S ≤ 2 ^ (m * n)) (hrcard : ∀ S, r S ≤ S.card)
    (hmono : ∀ {S T}, S ⊆ T → r S ≤ r T)
    (hsub : ∀ S T, r (S ∩ T) + r (S ∪ T) ≤ r S + r T)
    (hstep : ∀ S, r S < 2 ^ (m * n) → ∃ v ∉ S, r (insert v S) = r S + 1) :
    ∃ B : Finset V,
      r B = 2 ^ (m * n) ∧
        B.card = 2 ^ (m * n) ∧
          ∀ T : Finset V, r T = 2 ^ (m * n) → 2 ^ (m * n) ≤ T.card := by
  let ρ : ℕ := 2 ^ (m * n)
  have _ : r (∅ : Finset V) ≤ ρ := by
    simpa [ρ] using hrho (∅ : Finset V)
  have _ : r (∅ : Finset V) ≤ r (∅ : Finset V) := hmono (by intro x hx; exact hx)
  have _ : r ((∅ : Finset V) ∩ ∅) + r ((∅ : Finset V) ∪ ∅) ≤
      r (∅ : Finset V) + r (∅ : Finset V) :=
    hsub (∅ : Finset V) ∅
  have hbuild : ∀ k ≤ ρ, ∃ B : Finset V, r B = k ∧ B.card = k := by
    intro k
    induction k with
    | zero =>
        intro _hk
        exact ⟨∅, hzero, by simp⟩
    | succ k ih =>
        intro hk_succ
        have hk_lt : k < ρ := Nat.lt_of_succ_le hk_succ
        rcases ih (Nat.le_of_lt hk_lt) with ⟨B, hB_rank, hB_card⟩
        have hB_lt : r B < 2 ^ (m * n) := by
          simpa [ρ, hB_rank] using hk_lt
        rcases hstep B hB_lt with ⟨v, hv_not_mem, hinsert_rank⟩
        refine ⟨insert v B, ?_, ?_⟩
        · simpa [hB_rank, Nat.succ_eq_add_one] using hinsert_rank
        · rw [Finset.card_insert_of_notMem hv_not_mem, hB_card]
  rcases hbuild ρ le_rfl with ⟨B, hB_rank, hB_card⟩
  refine ⟨B, by simpa [ρ] using hB_rank, by simpa [ρ] using hB_card, ?_⟩
  intro T hT_rank
  simpa [hT_rank] using hrcard T

end Omega.Zeta
