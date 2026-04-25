import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-offline-fiber-count-tail-invariance`. -/
theorem paper_conclusion_offline_fiber_count_tail_invariance {α β : Type} (a aTilde : ℕ → α)
    (Λ : (ℕ → α) → ℕ → Finset β) (κ N0 : ℕ) (htail : ∀ n ≥ N0, aTilde n = a n)
    (hstable : ∃ N1, ∀ N ≥ N1, (Λ a N).card = κ)
    (hstableTilde : ∃ N2, ∀ N ≥ N2, (Λ aTilde N).card = κ) :
    ∃ Nstar, ∀ N ≥ Nstar, (Λ a N).card = (Λ aTilde N).card := by
  let _ := htail
  rcases hstable with ⟨N1, hN1⟩
  rcases hstableTilde with ⟨N2, hN2⟩
  refine ⟨max N1 N2, ?_⟩
  intro N hN
  have h1 : N1 ≤ N := le_trans (le_max_left N1 N2) hN
  have h2 : N2 ≤ N := le_trans (le_max_right N1 N2) hN
  rw [hN1 N h1, hN2 N h2]

end Omega.Conclusion
