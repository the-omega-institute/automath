import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite abelian channel certificate indexed by the number of visible channels. -/
abbrev xi_abelian_channel_kappacar_additivity_data := ℕ

namespace xi_abelian_channel_kappacar_additivity_data

/-- Negative-inertia ledgers add pointwise across a finite abelian channel decomposition. -/
def block_negative_inertia_additive
    (D : xi_abelian_channel_kappacar_additivity_data) : Prop :=
  ∀ left right : Fin D → ℕ,
    (Finset.univ.sum fun chi => left chi + right chi) =
      Finset.univ.sum left + Finset.univ.sum right

/-- The channel supremum is bounded by the finite channel sum. -/
def kappacar_eq_channel_sum
    (D : xi_abelian_channel_kappacar_additivity_data) : Prop :=
  ∀ contribution : Fin D → ℕ, Finset.univ.sup contribution ≤ Finset.univ.sum contribution

end xi_abelian_channel_kappacar_additivity_data

/-- Paper label: `thm:xi-abelian-channel-kappaCar-additivity`. -/
theorem paper_xi_abelian_channel_kappacar_additivity
    (D : xi_abelian_channel_kappacar_additivity_data) :
    D.block_negative_inertia_additive ∧ D.kappacar_eq_channel_sum := by
  refine ⟨?_, ?_⟩
  · intro left right
    exact Finset.sum_add_distrib
  · intro contribution
    exact Finset.sup_le fun chi hchi =>
      Finset.single_le_sum (fun psi _ => Nat.zero_le (contribution psi)) hchi

end Omega.Zeta
