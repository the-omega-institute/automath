import Mathlib.Tactic

namespace Omega.SPG

open Finset

theorem paper_spg_exact_screen_minima_are_matroid_bases
    {V : Type*} [DecidableEq V]
    (ρ : ℕ) (r : Finset V → ℕ)
    (hzero : r ∅ = 0)
    (_hrho : ∀ s, r s ≤ ρ)
    (hrcard : ∀ s, r s ≤ s.card)
    (_hmono : ∀ {s t : Finset V}, s ⊆ t → r s ≤ r t)
    (_hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t)
    (hstep : ∀ s, r s < ρ → ∃ v ∉ s, r (insert v s) = r s + 1) :
    ∃ B : Finset V, r B = ρ ∧ B.card = ρ ∧ ∀ T : Finset V, r T = ρ → ρ ≤ T.card := by
  have hbuild : ∀ n, n ≤ ρ → ∃ s : Finset V, r s = n ∧ s.card = n := by
    intro n
    induction' n with n ihn
    · intro _
      exact ⟨∅, hzero, by simp⟩
    · intro hn
      have hn' : n ≤ ρ := Nat.le_of_succ_le hn
      obtain ⟨s, hs_rank, hs_card⟩ := ihn hn'
      have hs_lt : r s < ρ := by
        rw [hs_rank]
        exact Nat.lt_of_succ_le hn
      obtain ⟨v, hv_not_mem, hv_rank⟩ := hstep s hs_lt
      refine ⟨insert v s, ?_, ?_⟩
      · simpa [hs_rank] using hv_rank
      · simp [hv_not_mem, hs_card]
  obtain ⟨B, hB_rank, hB_card⟩ := hbuild ρ le_rfl
  refine ⟨B, hB_rank, hB_card, ?_⟩
  intro T hT
  simpa [hT] using hrcard T

end Omega.SPG
