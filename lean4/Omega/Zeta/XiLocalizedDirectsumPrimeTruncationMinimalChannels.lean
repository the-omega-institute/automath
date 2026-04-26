import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- A localized direct-sum realization of the first `B` prime axes by `r` ledger channels is
modeled by an injective assignment of the `B` independent axes to the `r` available channels. -/
def xi_localized_directsum_prime_truncation_minimal_channels_realizationExists
    (B r : ℕ) : Prop :=
  Nonempty (Fin B ↪ Fin r)

/-- The coordinate-channel embedding supplied by a channel budget `B ≤ r`. -/
def xi_localized_directsum_prime_truncation_minimal_channels_forwardEmbedding
    {B r : ℕ} (h : B ≤ r) : Fin B ↪ Fin r where
  toFun i := ⟨i.1, lt_of_lt_of_le i.2 h⟩
  inj' := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin r => x.val) hij)

/-- Paper label: `thm:xi-localized-directsum-prime-truncation-minimal-channels`. -/
theorem paper_xi_localized_directsum_prime_truncation_minimal_channels
    (B r : ℕ) (hB : 1 ≤ B) :
    xi_localized_directsum_prime_truncation_minimal_channels_realizationExists B r ↔ B ≤ r := by
  let _ := hB
  constructor
  · rintro ⟨e⟩
    simpa using Fintype.card_le_of_embedding e
  · intro h
    exact ⟨xi_localized_directsum_prime_truncation_minimal_channels_forwardEmbedding h⟩

end Omega.Zeta
