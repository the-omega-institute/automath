import Omega.Zeta.XiTimePart69FiniteCharacterFamilySinglePrimitivePhase

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part69-finite-character-prime-ledger-finite-depth`. -/
theorem paper_xi_time_part69_finite_character_prime_ledger_finite_depth
    (S : Finset Nat) (r : Nat) (χ : Fin r → SupportedLocalizedIntegerGroup S) :
    ∃ phase : SupportedLocalizedIntegerGroup S, ∃ coeff : Fin r → ℤ,
      (∀ i : Fin r, χ i = coeff i • phase) ∧
        xi_time_part69_finite_character_family_single_primitive_phase_primitive_gcd_up_to_sign
          coeff := by
  simpa [xi_time_part69_finite_character_family_single_primitive_phase_statement] using
    paper_xi_time_part69_finite_character_family_single_primitive_phase S r χ

end Omega.Zeta
