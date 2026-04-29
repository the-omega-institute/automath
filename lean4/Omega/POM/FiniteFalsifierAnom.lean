import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-finite-falsifier-anom`. A finite decidable anomaly family either
vanishes everywhere or has an explicit falsifying index. -/
theorem paper_pom_finite_falsifier_anom {ι : Type*} [Fintype ι] (anom : ι → Prop)
    [∀ i, Decidable (anom i)] :
    (∀ i, anom i) ∨ ∃ i, ¬ anom i := by
  by_cases h : ∀ i, anom i
  · exact Or.inl h
  · exact Or.inr (not_forall.mp h)

end Omega.POM
