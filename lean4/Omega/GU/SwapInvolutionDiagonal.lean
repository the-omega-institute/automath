import Mathlib.Tactic

namespace Omega.GU

variable {X : Type*}

/-- Swap on a product: `(a,b) ↦ (b,a)`.
    prop:a2pm-isotropy-diagonal-su3 -/
def swap (p : X × X) : X × X := (p.2, p.1)

/-- Swap is its own inverse.
    prop:a2pm-isotropy-diagonal-su3 -/
theorem swap_swap (p : X × X) : swap (swap p) = p := by
  unfold swap
  rfl

/-- Swap is involutive.
    prop:a2pm-isotropy-diagonal-su3 -/
theorem swap_involutive : Function.Involutive (swap : X × X → X × X) := swap_swap

/-- Swap is bijective.
    prop:a2pm-isotropy-diagonal-su3 -/
theorem swap_bijective : Function.Bijective (swap : X × X → X × X) :=
  Function.Involutive.bijective swap_involutive

/-- A point is fixed by swap iff its coordinates are equal.
    prop:a2pm-isotropy-diagonal-su3 -/
theorem swap_fixed_point_iff (p : X × X) : swap p = p ↔ p.1 = p.2 := by
  unfold swap
  constructor
  · intro h
    exact (Prod.mk.inj h).1.symm
  · intro h
    ext
    · exact h.symm
    · exact h

/-- The fixed-point set of swap equals the diagonal.
    prop:a2pm-isotropy-diagonal-su3 -/
theorem swap_fixed_set_eq_diagonal :
    {p : X × X | swap p = p} = {p : X × X | p.1 = p.2} := by
  ext p
  exact swap_fixed_point_iff p

/-- Diagonal points are fixed by swap.
    prop:a2pm-isotropy-diagonal-su3 -/
theorem swap_fixed_diagonal (x : X) : swap (x, x) = (x, x) := by
  unfold swap
  rfl

/-- The diagonal embedding is injective.
    prop:a2pm-isotropy-diagonal-su3 -/
theorem diagonal_injective : Function.Injective (fun x : X => (x, x)) := by
  intro a b h
  exact (Prod.mk.inj h).1

/-- Paper package: A₂(±) isotropy diagonal (su(3) slice).
    prop:a2pm-isotropy-diagonal-su3 -/
theorem paper_a2pm_isotropy_diagonal_su3 :
    Function.Involutive (swap : X × X → X × X) ∧
    Function.Bijective (swap : X × X → X × X) ∧
    (∀ p : X × X, swap p = p ↔ p.1 = p.2) ∧
    {p : X × X | swap p = p} = {p : X × X | p.1 = p.2} ∧
    (∀ x : X, swap (x, x) = (x, x)) ∧
    Function.Injective (fun x : X => (x, x)) :=
  ⟨swap_involutive,
   swap_bijective,
   swap_fixed_point_iff,
   swap_fixed_set_eq_diagonal,
   swap_fixed_diagonal,
   diagonal_injective⟩

end Omega.GU
