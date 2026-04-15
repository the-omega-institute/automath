import Omega.Topos.IntrinsicHiddenStateLowerBound

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the intrinsic hidden-state lower bound in
    `2026_conservative_extension_chain_state_forcing_apal`.
    cor:intrinsic-hidden-state-lower-bound -/
theorem paper_conservative_extension_intrinsic_hidden_state_lower_bound_publication
    {A AVis R K : Type} [Fintype A] [Fintype R] [Fintype K] [DecidableEq AVis] [Nonempty A]
    (π : A → AVis) (r : A → R)
    (hinj : Function.Injective fun a => (π a, r a))
    (hfiber : ∀ a : A, Fintype.card {x // π x = π a} = Fintype.card K)
    (hsharp : ∃ f : A → AVis × K, Function.Injective f) :
    Fintype.card K ≤ Fintype.card R ∧
      ∃ f : A → AVis × K, Function.Injective f :=
  paper_conservative_extension_intrinsic_hidden_state_lower_bound π r hinj hfiber hsharp

end Omega.Topos
