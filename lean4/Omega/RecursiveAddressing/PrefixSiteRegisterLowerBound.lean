import Omega.SPG.RegisterLowerBound

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the full-resolution recovery register bound in the recursive
    addressing paper. The lower-bound clause is discharged by the generic fiber-vs-register lemma,
    while sharpness is carried by an explicit recovery embedding with register `H`.
    thm:prefix-site-register-lower-bound -/
theorem paper_recursive_addressing_prefix_site_register_lower_bound
    {A Avis R H : Type} [Fintype A] [Fintype R] [Fintype H] [DecidableEq Avis] [Nonempty A]
    (q : A → Avis) (r : A → R)
    (hinj : Function.Injective fun a => (q a, r a))
    (hfiber : ∀ a : A, Fintype.card {x // q x = q a} = Fintype.card H)
    (hsharp : ∃ f : A → Avis × H, Function.Injective f) :
    Fintype.card H ≤ Fintype.card R ∧
      ∃ f : A → Avis × H, Function.Injective f := by
  classical
  refine ⟨?_, hsharp⟩
  let a0 : A := Classical.choice ‹Nonempty A›
  have hcard : Fintype.card {x // q x = q a0} = Fintype.card H := hfiber a0
  have hle :=
    Omega.SPG.RegisterLowerBound.fiber_card_le_register_card (Ω := A) (Y := Avis) (R := R)
      q r hinj (q a0)
  simpa [hcard] using hle

/-- Paper-facing wrapper with the exact theorem slug used in the manuscript.
    thm:prefix-site-register-lower-bound -/
theorem paper_prefix_site_register_lower_bound
    {A Avis R H : Type} [Fintype A] [Fintype R] [Fintype H] [DecidableEq Avis] [Nonempty A]
    (q : A → Avis) (r : A → R)
    (hinj : Function.Injective fun a => (q a, r a))
    (hfiber : ∀ a : A, Fintype.card {x // q x = q a} = Fintype.card H)
    (hsharp : ∃ f : A → Avis × H, Function.Injective f) :
    Fintype.card H ≤ Fintype.card R ∧ ∃ f : A → Avis × H, Function.Injective f := by
  exact paper_recursive_addressing_prefix_site_register_lower_bound q r hinj hfiber hsharp

end Omega.RecursiveAddressing
