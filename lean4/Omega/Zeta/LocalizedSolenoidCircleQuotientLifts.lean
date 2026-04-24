import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersCrossHomClassification
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Zeta

/-- Multiplication by an integer on the chapter-local `ℤ` model of `G_S`. -/
private def localizedCircleLiftHom (n : ℤ) : ℤ →+ ℤ where
  toFun z := z * n
  map_zero' := by simp
  map_add' x y := by ring

private theorem not_localizedMissingPrime_self (S : Finset Nat) : ¬ localizedMissingPrime S S := by
  rintro ⟨p, hpS, hpNotS⟩
  exact hpNotS hpS

/-- In the simplified localized model, there is a unique self-cross-hom with prescribed value on
`1`, and for prime scalars the localized quotient ledger records whether the prime is inverted or
contributes a genuine finite quotient factor. -/
theorem paper_xi_time_part62db_localized_solenoid_circle_quotient_lifts
    (S : Finset Nat) (p : Nat) (hp : Nat.Prime p) :
    (∃! φ : LocalizedCrossHom S S, localizedCrossHomScalar φ = p) ∧
      (p ∈ S ↔ localizedIndex S p = 1) ∧
      (p ∉ S ↔ localizedIndex S p = p) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨localizedCircleLiftHom p, ?_⟩, ?_, ?_⟩
    · intro hMissing
      exact (not_localizedMissingPrime_self S hMissing).elim
    · simp [localizedCrossHomScalar, localizedCircleLiftHom]
    · intro φ hφ
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro z
      have hz := localizedCrossHom_eq_mul φ z
      rw [hφ] at hz
      simpa [localizedCircleLiftHom] using hz
  · exact (paper_xi_localized_quotient_index_prime_recovery S hp).1
  · exact (paper_xi_localized_quotient_index_prime_recovery S hp).2

end Omega.Zeta
