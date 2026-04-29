import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable instance instFintypeFiber {X Y : Type} [Fintype Y] (f : Y → X) (x : X) :
    Fintype {y // f y = x} := Fintype.ofFinite _

/-- Paper label: `thm:xi-bdry-free-involution-odd-fiber-obstruction-min-cover`. -/
theorem paper_xi_bdry_free_involution_odd_fiber_obstruction_min_cover {X Y : Type}
    [Fintype X] [Fintype Y] (f : Y → X) (σ : Y → Y) (hσ : Function.Involutive σ)
    (hfree : ∀ y, σ y ≠ y) (hcompat : ∀ y, f (σ y) = f y) :
    ∀ x, Even (Fintype.card {y // f y = x}) := by
  intro x
  classical
  let fiber := {y // f y = x}
  let τ : fiber → fiber := fun y => ⟨σ y.1, by simpa [y.2] using hcompat y.1⟩
  have hτ : Function.Involutive τ := by
    intro y
    ext
    simp [τ, hσ y.1]
  have hτfree : ∀ y : fiber, τ y ≠ y := by
    intro y hy
    exact hfree y.1 (congrArg Subtype.val hy)
  let τperm : Equiv.Perm fiber := Function.Involutive.toPerm τ hτ
  have hnotOdd : ¬ Odd (Fintype.card fiber) := by
    intro hOdd
    have hcard : ¬ 2 ∣ Fintype.card fiber := by
      intro hdiv
      exact (Nat.not_even_iff_odd.mpr hOdd) ((even_iff_two_dvd).2 hdiv)
    have hτpow : τperm ^ (2 ^ 1) = 1 := by
      ext y
      simp [τperm, pow_two, hτ y]
    obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcard hτpow
    exact hτfree y hy
  exact Nat.not_odd_iff_even.mp hnotOdd

end Omega.Zeta
