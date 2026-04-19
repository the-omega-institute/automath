import Mathlib.Tactic
import Omega.Folding.StableSyntax

namespace Omega.GU

/-- Chapter-local tail cutoff. At saturation the cutoff length is exactly `m`, so the residual
tail length is `K m - m = 0`. -/
def K (m : Nat) : Nat := m

/-- Saturation means the tail cutoff no longer exceeds the visible window. -/
def saturation_point (m : Nat) : Prop := K m ≤ m

/-- The saturation predicate is decidable because it is just a natural-number inequality. -/
instance instDecidableSaturationPoint (m : Nat) : Decidable (saturation_point m) := by
  unfold saturation_point K
  infer_instance

/-- The zero fiber is modeled by the surviving tail language after removing the redundant
inequality constraint at a saturation point. -/
def foldbin_zero_fiber (m : Nat) : Type := X (if saturation_point m then K m - m else 0)

/-- At a saturation point the inequality constraint is redundant, so the zero fiber is canonically
the tail space `X (K m - m)`. -/
def paper_window6_saturation_maxfiber_canonical_xl :
    ∀ m, saturation_point m → foldbin_zero_fiber m ≃ X (K m - m) := by
  intro m hm
  simpa [foldbin_zero_fiber, hm] using Equiv.refl (X (K m - m))

end Omega.GU
