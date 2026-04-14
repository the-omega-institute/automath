import Mathlib.Data.Fintype.Card

namespace Omega.SPG.RegisterLowerBound

/-- Any auxiliary register making a quotient injective must separate each individual fiber. -/
theorem fiber_card_le_register_card
    {Ω Y R : Type} [Fintype Ω] [Fintype R] [DecidableEq Y]
    (f : Ω → Y) (r : Ω → R)
    (hinj : Function.Injective fun ω => (f ω, r ω))
    (y : Y) :
    Fintype.card {ω // f ω = y} ≤ Fintype.card R := by
  let g : {ω // f ω = y} → R := fun ω => r ω.1
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply hinj
    exact Prod.ext (a.2.trans b.2.symm) h
  simpa [g] using Fintype.card_le_of_injective g hg

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the register-lower-bound corollary in the scan-projection paper.
    thm:register-lower-bound -/
theorem paper_scan_projection_address_register_lower_bound
    {Ω Y R : Type} [Fintype Ω] [Fintype R] [DecidableEq Y]
    (f : Ω → Y) (r : Ω → R)
    (hinj : Function.Injective fun ω => (f ω, r ω))
    (y : Y) :
    Fintype.card {ω // f ω = y} ≤ Fintype.card R :=
  fiber_card_le_register_card f r hinj y

end Omega.SPG.RegisterLowerBound
