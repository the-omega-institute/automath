import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9xb-holographic-image-strict-self-affine-decomposition`. -/
theorem paper_xi_time_part9xb_holographic_image_strict_self_affine_decomposition {E T : Type*}
    [Fintype E] [DecidableEq E] (n : Nat) (_hn : 1 ≤ n) (X : Set T)
    (cyl : (Fin n → E) → Set T) (hcover : X = Set.iUnion cyl)
    (hdisj : ∀ w v, w ≠ v → Disjoint (cyl w) (cyl v)) :
    X = Set.iUnion cyl ∧
      (∀ w v, w ≠ v → Disjoint (cyl w) (cyl v)) ∧
        Fintype.card (Fin n → E) = Fintype.card E ^ n := by
  refine ⟨hcover, hdisj, ?_⟩
  rw [Fintype.card_fun, Fintype.card_fin]

end Omega.Zeta
