import Omega.Zeta.XiPhasePrefixCollisionLowerBound

namespace Omega.Zeta

/-- Paper label: `cor:xi-phase-prefix-clarity-horizon`. If every dyadic prefix box has occupancy
at most `1`, the existing occupied-box lower bound forces the resolution horizon `2^m` to be at
least a constant multiple of `T² log T`. -/
theorem paper_xi_phase_prefix_clarity_horizon (T : Real) (m : Nat) (Gamma : Finset Real)
    (hT : 1 <= T)
    (hGamma : ∀ gamma ∈ Gamma, T < gamma ∧ gamma <= 2 * T)
    (hcard : T * Real.log T <= (Gamma.card : Real))
    (hNoCollision : forall a : Nat,
      ((Gamma.filter fun gamma =>
          Nat.floor ((2 : Real) ^ m * ((Real.arctan gamma) / Real.pi + 1 / 2)) = a).card :
        Real) <= 1) :
    ∃ C > 0, T ^ 2 * Real.log T <= C * (2 : Real) ^ m := by
  obtain ⟨c, hc, a, ha⟩ :=
    paper_xi_phase_prefix_collision_lower_bound T m Gamma hT hGamma hcard
  let paper_xi_phase_prefix_clarity_horizon_occupied : Real :=
    ((Gamma.filter fun gamma =>
        Nat.floor ((2 : Real) ^ m * ((Real.arctan gamma) / Real.pi + 1 / 2)) = a).card : Real)
  have hoccupied_le : paper_xi_phase_prefix_clarity_horizon_occupied <= 1 := by
    simpa [paper_xi_phase_prefix_clarity_horizon_occupied] using hNoCollision a
  have hscaled_le_one : c * T ^ 2 * Real.log T / (2 : Real) ^ m <= 1 := by
    exact le_trans (by simpa [paper_xi_phase_prefix_clarity_horizon_occupied] using ha) hoccupied_le
  have hpow_pos : 0 < (2 : Real) ^ m := by
    positivity
  have hscaled : c * (T ^ 2 * Real.log T) <= (2 : Real) ^ m := by
    have htmp :=
      mul_le_mul_of_nonneg_right hscaled_le_one (le_of_lt hpow_pos)
    have hpow_ne : (2 : Real) ^ m ≠ 0 := ne_of_gt hpow_pos
    simpa [div_eq_mul_inv, hpow_ne, mul_assoc, mul_left_comm, mul_comm] using htmp
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  have hbound_mul :
      c⁻¹ * (c * (T ^ 2 * Real.log T)) <= c⁻¹ * (2 : Real) ^ m := by
    exact mul_le_mul_of_nonneg_left hscaled (by positivity)
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hbound :
      T ^ 2 * Real.log T <= c⁻¹ * (2 : Real) ^ m := by
    simpa [hc_ne, mul_assoc, mul_left_comm, mul_comm] using hbound_mul
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbound

end Omega.Zeta
