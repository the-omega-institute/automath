import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:pom-fiber-invariance`.
An observable is constant on the fibers of `Foldm` exactly when it factors through `Foldm`; the
fold-invariant subalgebra hypothesis packages the third clause. -/
theorem paper_pom_fiber_invariance {α β : Type*} (Foldm : α → β) (Bm : Set (α → ℝ)) (g : α → ℝ)
    (hBm : ∀ f : α → ℝ, f ∈ Bm ↔ ∃ gbar : β → ℝ, f = fun a => gbar (Foldm a)) :
    (((∀ a b, Foldm a = Foldm b → g a = g b) ↔ ∃ gbar : β → ℝ, g = fun a => gbar (Foldm a)) ∧
      ((∃ gbar : β → ℝ, g = fun a => gbar (Foldm a)) ↔ g ∈ Bm)) := by
  classical
  refine ⟨?_, (hBm g).symm⟩
  constructor
  · intro hconst
    let gbar : β → ℝ := fun b =>
      if h : ∃ a, Foldm a = b then g (Classical.choose h) else 0
    refine ⟨gbar, funext ?_⟩
    intro a
    have h : ∃ a', Foldm a' = Foldm a := ⟨a, rfl⟩
    rw [show gbar (Foldm a) = if h : ∃ a', Foldm a' = Foldm a then g (Classical.choose h) else 0 by
      rfl]
    rw [dif_pos h]
    exact (hconst (Classical.choose h) a (Classical.choose_spec h)).symm
  · rintro ⟨gbar, rfl⟩ a b hab
    simp [hab]

end Omega.POM
