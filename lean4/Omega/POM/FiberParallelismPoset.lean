import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace Omega.POM

/-- A finite certificate that a schedule has enough layers for a critical chain and enough
layer-slots for all events. -/
def pom_fiber_parallelism_poset_statement : Prop :=
  ∀ N ht wd depth : ℕ,
    Nonempty (Fin ht ↪ Fin depth) →
      Nonempty (Fin N ↪ Fin depth × Fin wd) →
        ht ≤ depth ∧ N ≤ depth * wd

/-- Paper label: `cor:pom-fiber-parallelism-poset`. -/
theorem paper_pom_fiber_parallelism_poset : pom_fiber_parallelism_poset_statement := by
  intro N ht wd depth hchain hpacking
  constructor
  · rcases hchain with ⟨chainEmbedding⟩
    simpa using Fintype.card_le_of_injective chainEmbedding chainEmbedding.injective
  · rcases hpacking with ⟨packingEmbedding⟩
    have hcard :=
      Fintype.card_le_of_injective packingEmbedding packingEmbedding.injective
    simpa [Fintype.card_prod] using hcard

end Omega.POM
