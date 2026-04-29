import Mathlib.Tactic

namespace Omega.Zeta

/-- Kernel equality stripped to its additive consequence: `C₁ - C₂` is constant. -/
def xi_pick_kernel_gauge_rigidity_kernelEqual {D A : Type*} [Sub A] (C1 C2 : D → A) :
    Prop :=
  ∀ w z : D, C1 w - C2 w = C1 z - C2 z

/-- Paper label: `thm:xi-pick-kernel-gauge-rigidity`. -/
theorem paper_xi_pick_kernel_gauge_rigidity {D A : Type*} [Nonempty D] [AddCommGroup A]
    (C1 C2 : D → A) (hK : xi_pick_kernel_gauge_rigidity_kernelEqual C1 C2) :
    ∃ η : A, ∀ w : D, C1 w = C2 w + η := by
  let base : D := Classical.choice ‹Nonempty D›
  refine ⟨C1 base - C2 base, ?_⟩
  intro w
  have hconst : C1 w - C2 w = C1 base - C2 base := hK w base
  calc
    C1 w = C2 w + (C1 w - C2 w) := by abel
    _ = C2 w + (C1 base - C2 base) := by rw [hconst]

end Omega.Zeta
