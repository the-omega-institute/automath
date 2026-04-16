import Mathlib.Data.Fintype.Card

namespace Omega.SPG

/-- A truncated prime-register with `(E + 1)^k` states cannot injectively encode more than
    `(E + 1)^k` classes. -/
theorem paper_spg_prime_register_budget_lower_bound (p r k E : ℕ)
    (henc : ∃ f : Fin (p ^ r) → Fin ((E + 1) ^ k), Function.Injective f) :
    p ^ r ≤ (E + 1) ^ k := by
  rcases henc with ⟨f, hf⟩
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

end Omega.SPG
