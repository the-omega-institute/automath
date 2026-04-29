import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

/-- Concrete carrier-quotient package for the active-character kernel intersection.  The
projection `carrierProjection` is the quotient map by the carrier kernel, and
`carrierDensity` is the descended density on that quotient. -/
structure xi_time_part64aa_abelian_minimal_deviation_carrier_quotient_data where
  Label : Type
  Carrier : Type
  carrierPoint : Carrier
  density : Label → ℂ
  carrierProjection : Label → Carrier
  carrierDensity : Carrier → ℂ
  density_factorization : ∀ x, density x = carrierDensity (carrierProjection x)
  carrier_refines_every_density_quotient :
    ∀ {Q : Type} (π : Label → Q),
      (∀ x y, π x = π y → density x = density y) →
        ∀ x y, π x = π y → carrierProjection x = carrierProjection y

namespace xi_time_part64aa_abelian_minimal_deviation_carrier_quotient_data

/-- The density descends to the carrier quotient. -/
def density_factors_through_carrier
    (D : xi_time_part64aa_abelian_minimal_deviation_carrier_quotient_data) : Prop :=
  ∀ x, D.density x = D.carrierDensity (D.carrierProjection x)

/-- Any quotient through which the density is constant admits a map to the carrier quotient. -/
def carrier_is_unique_minimal
    (D : xi_time_part64aa_abelian_minimal_deviation_carrier_quotient_data) : Prop :=
  ∀ {Q : Type} (π : D.Label → Q),
    (∀ x y, π x = π y → D.density x = D.density y) →
      ∃ Φ : Q → D.Carrier, ∀ x, Φ (π x) = D.carrierProjection x

end xi_time_part64aa_abelian_minimal_deviation_carrier_quotient_data

/-- Paper label:
`thm:xi-time-part64aa-abelian-minimal-deviation-carrier-quotient`. -/
theorem paper_xi_time_part64aa_abelian_minimal_deviation_carrier_quotient
    (D : xi_time_part64aa_abelian_minimal_deviation_carrier_quotient_data) :
    D.density_factors_through_carrier ∧ D.carrier_is_unique_minimal := by
  constructor
  · exact D.density_factorization
  · intro Q π hπ
    classical
    let Φ : Q → D.Carrier := fun q =>
      if hq : ∃ x, π x = q then D.carrierProjection (Classical.choose hq) else D.carrierPoint
    refine ⟨Φ, ?_⟩
    intro x
    dsimp [Φ]
    have hx : ∃ y, π y = π x := ⟨x, rfl⟩
    rw [dif_pos hx]
    exact D.carrier_refines_every_density_quotient π hπ (Classical.choose hx) x
      (Classical.choose_spec hx)

end Omega.Zeta
