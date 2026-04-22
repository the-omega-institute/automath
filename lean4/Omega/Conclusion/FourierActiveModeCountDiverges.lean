import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence

namespace Omega.Conclusion

/-- The collision-driven lower bound for the number of active nonzero Fourier modes. -/
def fourierActiveModeCountLowerBound (M Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  M m * Col m - 1

/-- The natural-scale total-variation term `√M_m · TV_m`. -/
noncomputable def conclusion_foldbin_natural_scale_tv_impossible_term (M tv : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (M m) * tv m

/-- If the collision scale `M_m * Col_m` diverges, then the linear lower bound
`M_m * Col_m - 1` diverges as well. -/
private theorem fourierActiveModeCountLowerBound_diverges
    (M Col : ℕ → ℝ)
    (hGrowth : NatDivergesToInfinity (binfoldCollisionScaleTerm M Col)) :
    NatDivergesToInfinity (fourierActiveModeCountLowerBound M Col) := by
  intro K
  obtain ⟨m, hm⟩ := hGrowth (K + 1)
  refine ⟨m, ?_⟩
  have hm' : (K : ℝ) + 1 ≤ M m * Col m := by
    simpa [binfoldCollisionScaleTerm, Nat.cast_add] using hm
  dsimp [fourierActiveModeCountLowerBound]
  linarith

/-- The nonzero Fourier support is bounded below by the collision mass minus the zero mode, so
once `M_m * Col_m` diverges the active-mode count must diverge too.
    cor:conclusion-fourier-active-mode-count-diverges -/
theorem paper_conclusion_fourier_active_mode_count_diverges
    (Nnz M Col : ℕ → ℝ)
    (hLower : ∀ m, fourierActiveModeCountLowerBound M Col m ≤ Nnz m)
    (hGrowth : NatDivergesToInfinity (binfoldCollisionScaleTerm M Col)) :
    (∀ m, M m * Col m - 1 ≤ Nnz m) ∧ NatDivergesToInfinity Nnz := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa [fourierActiveModeCountLowerBound] using hLower m
  · intro K
    obtain ⟨m, hm⟩ := fourierActiveModeCountLowerBound_diverges M Col hGrowth K
    exact ⟨m, hm.trans (hLower m)⟩

private theorem conclusion_foldbin_natural_scale_tv_impossible_half_sqrt_lower
    {K : ℕ} {x : ℝ} (hSq : ((2 * K : ℝ) ^ 2) ≤ x) : (K : ℝ) ≤ Real.sqrt x / 2 := by
  have hsqrt : (2 * K : ℝ) ≤ Real.sqrt x := by
    have hsqrt' := Real.sqrt_le_sqrt hSq
    have htwo_nonneg : 0 ≤ (2 * K : ℝ) := by positivity
    rw [Real.sqrt_sq_eq_abs] at hsqrt'
    simpa [abs_of_nonneg htwo_nonneg] using hsqrt'
  nlinarith

/-- If the collision scale diverges, then the natural-scale total-variation quantity
`√M_m · TV_m` cannot stay bounded once it dominates half of the scaled `L²` excess. This is the
abstract conclusion-level wrapper for the passage from `‖p_m - u‖₂` to total variation. -/
theorem paper_conclusion_foldbin_natural_scale_tv_impossible :
    ∀ M Col tv : ℕ → ℝ,
      (∀ m, 1 ≤ binfoldCollisionScaleTerm M Col m) →
      NatDivergesToInfinity (binfoldCollisionScaleTerm M Col) →
      (∀ m,
        Real.sqrt (binfoldScaledL2Term M Col m) / 2 ≤
          conclusion_foldbin_natural_scale_tv_impossible_term M tv m) →
      NatDivergesToInfinity (conclusion_foldbin_natural_scale_tv_impossible_term M tv) := by
  intro M Col tv hCollisionLower hCollisionDiv hTvLower
  intro K
  obtain ⟨m, hm⟩ := hCollisionDiv (((2 * K) * (2 * K)) + 1)
  refine ⟨m, ?_⟩
  have hsq :
      ((2 * K : ℝ) ^ 2) ≤ binfoldScaledL2Term M Col m := by
    have hm' : ((((2 * K) * (2 * K)) + 1 : ℕ) : ℝ) ≤ binfoldCollisionScaleTerm M Col m := by
      simpa [Nat.cast_add, Nat.cast_mul] using hm
    have hm'' : (4 : ℝ) * K * K + 1 ≤ binfoldCollisionScaleTerm M Col m := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hm'
    have hle : (4 : ℝ) * K * K ≤ binfoldCollisionScaleTerm M Col m - 1 := by
      linarith
    calc
      ((2 * K : ℝ) ^ 2) = (4 : ℝ) * K * K := by ring
      _ ≤ binfoldScaledL2Term M Col m := by
        simpa [binfoldScaledL2Term, binfoldCollisionScaleTerm] using hle
  have hk : (K : ℝ) ≤ Real.sqrt (binfoldScaledL2Term M Col m) / 2 :=
    conclusion_foldbin_natural_scale_tv_impossible_half_sqrt_lower hsq
  exact le_trans hk (hTvLower m)

end Omega.Conclusion
