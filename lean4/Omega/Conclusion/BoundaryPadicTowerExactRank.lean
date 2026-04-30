import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-level and inverse-limit data for a `p`-adic boundary equation tower. Each
finite fiber is identified with `Fin (p^(ell*r))`, so its exact size is built into the datum. -/
structure BoundaryPadicTowerData where
  p : Nat
  r : Nat
  fiber : Nat → Type
  fiberFintype : ∀ ell, Fintype (fiber ell)
  fiberEquiv : ∀ ell, fiber ell ≃ Fin (p ^ (ell * r))
  profiniteFiber : Type
  profiniteWitness : profiniteFiber

attribute [instance] BoundaryPadicTowerData.fiberFintype

/-- Every finite layer in the boundary `p`-adic tower has the exact cardinality `p^(ell*r)`, and
the compatible inverse-limit fiber is nonempty once a compatible thread is given.
    thm:conclusion-boundary-padic-tower-exact-rank -/
theorem paper_conclusion_boundary_padic_tower_exact_rank (D : BoundaryPadicTowerData) :
    (∀ ell, Fintype.card (D.fiber ell) = D.p ^ (ell * D.r)) ∧ Nonempty D.profiniteFiber := by
  refine ⟨?_, ⟨D.profiniteWitness⟩⟩
  intro ell
  simpa using Fintype.card_congr (D.fiberEquiv ell)

/-- Paper label: `cor:conclusion-boundary-padic-tower-exact-slope-rigidity`. -/
theorem paper_conclusion_boundary_padic_tower_exact_slope_rigidity
    (p r ell card_l card_next fiberCard : ℕ) (hp : 0 < p) (hell : 1 ≤ ell)
    (hcard_l : card_l = p ^ (ell * r))
    (hcard_next : card_next = p ^ ((ell + 1) * r)) (hfiber : fiberCard = p ^ r) :
    card_next = card_l * p ^ r ∧ fiberCard = p ^ r := by
  have _ : 0 < p := hp
  have _ : 1 ≤ ell := hell
  refine ⟨?_, hfiber⟩
  rw [hcard_l, hcard_next]
  have hmul : (ell + 1) * r = ell * r + r := by
    rw [Nat.add_mul, one_mul]
  rw [hmul, pow_add]

end Omega.Conclusion
