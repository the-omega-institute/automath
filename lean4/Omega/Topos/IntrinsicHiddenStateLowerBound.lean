import Omega.SPG.RegisterLowerBound

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the intrinsic hidden-state lower bound.
    cor:intrinsic-hidden-state-lower-bound -/
theorem paper_conservative_extension_intrinsic_hidden_state_lower_bound
    {A AVis R K : Type} [Fintype A] [Fintype R] [Fintype K] [DecidableEq AVis] [Nonempty A]
    (π : A → AVis) (r : A → R)
    (hinj : Function.Injective fun a => (π a, r a))
    (hfiber : ∀ a : A, Fintype.card {x // π x = π a} = Fintype.card K)
    (hsharp : ∃ f : A → AVis × K, Function.Injective f) :
    Fintype.card K ≤ Fintype.card R ∧
      ∃ f : A → AVis × K, Function.Injective f := by
  classical
  refine ⟨?_, hsharp⟩
  let a0 : A := Classical.choice ‹Nonempty A›
  have hcard : Fintype.card {x // π x = π a0} = Fintype.card K := hfiber a0
  have hle :=
    Omega.SPG.RegisterLowerBound.fiber_card_le_register_card (Ω := A) (Y := AVis) (R := R)
      π r hinj (π a0)
  simpa [hcard] using hle

end Omega.Topos
