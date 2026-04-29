import Mathlib.Data.Fintype.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-compactness-by-fundamental-circle`. -/
theorem paper_xi_leyang_compactness_by_fundamental_circle {ι G : Type} [Fintype ι]
    (isCompactSemisimpleClass : G -> Prop) (fundamentalCircleTest : ι -> G -> Prop)
    (h_forward : ∀ g, isCompactSemisimpleClass g -> ∀ i, fundamentalCircleTest i g)
    (h_reverse : ∀ g, (∀ i, fundamentalCircleTest i g) -> isCompactSemisimpleClass g) :
    ∀ g, isCompactSemisimpleClass g ↔ ∀ i, fundamentalCircleTest i g := by
  intro g
  exact ⟨h_forward g, h_reverse g⟩

end Omega.Zeta
