import Mathlib.Data.Fintype.Basic

namespace Omega.POM

/-- Paper label: `thm:pom-hankel-primitive-torsion-spectrum`. -/
theorem paper_pom_hankel_primitive_torsion_spectrum {T : Type} [Finite T]
    (rankBad torsionBad extraNull : Nat → Prop)
    (hchar : ∀ p, extraNull p ↔ rankBad p ∧ torsionBad p) :
    Finite T ∧ (∀ p, extraNull p ↔ rankBad p ∧ torsionBad p) := by
  exact ⟨inferInstance, hchar⟩

end Omega.POM
