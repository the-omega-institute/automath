import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- If the circle-dimension axis is identically `1` on finite prime sets, then no function of
that single invariant can uniformly bound finite support size.
    prop:conclusion-circle-dimension-prime-ledger-strict-orthogonality -/
theorem paper_conclusion_circle_dimension_prime_ledger_strict_orthogonality
    (cdim : Finset ℕ → ℕ) (hconst : ∀ S : Finset ℕ, cdim S = 1) :
    ¬ ∃ F : ℕ → ℕ, ∀ S : Finset ℕ, S.card ≤ F (cdim S) := by
  intro hbound
  rcases hbound with ⟨F, hF⟩
  have hrange : (Finset.range (F 1 + 1)).card ≤ F 1 := by
    simpa [hconst] using hF (Finset.range (F 1 + 1))
  simp at hrange

end Omega.Conclusion
