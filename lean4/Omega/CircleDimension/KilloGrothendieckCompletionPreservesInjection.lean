import Mathlib

namespace Omega.CircleDimension

/-- Equality on Grothendieck-completion representatives, expressed by adding a common witness on
the right. -/
def killo_grothendieck_completion_preserves_injection_completion_eq
    {M : Type*} [AddCancelCommMonoid M] (x y : M × M) : Prop :=
  ∃ c : M, x.1 + y.2 + c = y.1 + x.2 + c

/-- The Grothendieck-completion representative induced by an additive monoid homomorphism. -/
def killo_grothendieck_completion_preserves_injection_completion_map
    {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) (x : M) : N × N :=
  (f x, 0)

/-- An injective homomorphism between cancellative commutative monoids stays injective after
passing to Grothendieck-completion representatives. The proof reduces equality in the completion
to a cancellation statement in the target. -/
theorem paper_killo_grothendieck_completion_preserves_injection
    {M N : Type*} [AddCancelCommMonoid M] [AddCancelCommMonoid N]
    (f : M →+ N) (hf : Function.Injective f) :
    ∀ {x y : M},
      killo_grothendieck_completion_preserves_injection_completion_eq
        (killo_grothendieck_completion_preserves_injection_completion_map f x)
        (killo_grothendieck_completion_preserves_injection_completion_map f y) →
      x = y := by
  intro x y hxy
  rcases hxy with ⟨c, hc⟩
  have hfxfy : f x + c = f y + c := by
    simpa [killo_grothendieck_completion_preserves_injection_completion_eq,
      killo_grothendieck_completion_preserves_injection_completion_map, add_assoc] using hc
  exact hf (add_right_cancel hfxfy)

end Omega.CircleDimension
