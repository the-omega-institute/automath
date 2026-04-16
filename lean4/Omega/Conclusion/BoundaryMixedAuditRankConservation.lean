import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace Omega.Conclusion

/-- An injective mixed transcript/register encoding of `p^r` classes into
    `p^q × (E + 1)^k` states forces the expected mixed budget lower bound. -/
theorem paper_conclusion_boundary_mixed_audit_rank_conservation :
    ∀ p q r k E : ℕ,
    (∃ encode : Fin (p ^ r) → Fin (p ^ q) × Fin ((E + 1) ^ k), Function.Injective encode) →
      p ^ r ≤ p ^ q * (E + 1) ^ k := by
  intro p q r k E henc
  rcases henc with ⟨encode, hinj⟩
  simpa [Fintype.card_fin, Fintype.card_prod] using Fintype.card_le_of_injective encode hinj

end Omega.Conclusion
