import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-horizon-offcircle-pair-bound-by-kappa`. -/
theorem paper_xi_horizon_offcircle_pair_bound_by_kappa {α : Type*} [DecidableEq α]
    (inside outside : Finset α) (κ : Nat)
    (certIn : {z : α // z ∈ inside} → Fin κ)
    (certOut : {z : α // z ∈ outside} → Fin κ)
    (hinjIn : Function.Injective certIn) (hinjOut : Function.Injective certOut) :
    inside.card ≤ κ ∧ outside.card ≤ κ := by
  constructor
  · have hcard :
        Fintype.card {z : α // z ∈ inside} ≤ Fintype.card (Fin κ) :=
      Fintype.card_le_of_injective certIn hinjIn
    have hinside : Fintype.card {z : α // z ∈ inside} = inside.card :=
      Fintype.card_of_subtype inside (by intro z; simp)
    simpa [hinside] using hcard
  · have hcard :
        Fintype.card {z : α // z ∈ outside} ≤ Fintype.card (Fin κ) :=
      Fintype.card_le_of_injective certOut hinjOut
    have houtside : Fintype.card {z : α // z ∈ outside} = outside.card :=
      Fintype.card_of_subtype outside (by intro z; simp)
    simpa [houtside] using hcard

end Omega.Zeta
