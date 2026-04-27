import Omega.Zeta.XiTimePart58aDirichletMinimalWitnessWorstExponent

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-time-part9zm-parity-character-breaks-square-root-barrier`. -/
theorem paper_xi_time_part9zm_parity_character_breaks_square_root_barrier :
    ∃ ρ : ℝ, ρ ^ 3 - 2 * ρ ^ 2 - 1 = 0 ∧
      xi_real_input_40_collision_minimal_modulus_two_witness_phi < ρ ∧
      ρ < 1 + Real.sqrt 2 := by
  rcases paper_xi_real_input_40_collision_minimal_modulus_two_witness with
    ⟨ρ, hroot, hphi, hupper, _⟩
  refine ⟨ρ, ?_, hphi, hupper⟩
  simpa [xi_real_input_40_collision_minimal_modulus_two_witness_poly] using hroot

end

end Omega.Zeta
