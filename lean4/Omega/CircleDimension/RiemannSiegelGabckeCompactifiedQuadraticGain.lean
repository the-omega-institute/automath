import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic
import Omega.CircleDimension.RiemannSiegelGabckeLocalZeroStability

namespace Omega.CircleDimension

/-- Compactified readout of a local zero location. -/
noncomputable def rsGabckeCompactify (t : ℝ) : ℝ :=
  Real.arctan t / Real.pi

/-- Paper label: `cor:cdim-rs-gabcke-compactified-quadratic-gain`. On a certified interval contained
in the nonnegative axis, the compactified approximate-zero displacement inherits the local-zero
stability bound together with the quadratic decay of the `arctan` derivative. -/
theorem paper_cdim_rs_gabcke_compactified_quadratic_gain
    (γ ρ m eK eK1 : ℝ)
    (hρ : 0 < ρ) (hm : 0 < m) (hleft : 0 ≤ γ - ρ)
    (heK : |eK| ≤ m * ρ) (heK1 : |eK1| ≤ m * ρ) :
    let γK := rsGabckeApproxZero γ m eK
    let γK1 := rsGabckeApproxZero γ m eK1
    |rsGabckeCompactify γK1 - rsGabckeCompactify γK| ≤
      |eK1 - eK| / (Real.pi * m * (1 + (γ - ρ) ^ 2)) := by
  rcases paper_cdim_rs_gabcke_local_zero_stability γ ρ m eK eK1 hρ hm heK heK1 with
    ⟨_, _, _, hγK_lower, hγK_upper, _, _, _, hγK1_lower, hγK1_upper, _, _, hstep_bound⟩
  let I := Set.Icc (γ - ρ) (γ + ρ)
  let γK := rsGabckeApproxZero γ m eK
  let γK1 := rsGabckeApproxZero γ m eK1
  have hγK_mem : γK ∈ I := by
    exact ⟨hγK_lower, hγK_upper⟩
  have hγK1_mem : γK1 ∈ I := by
    exact ⟨hγK1_lower, hγK1_upper⟩
  have hdiff :
      ‖rsGabckeCompactify γK1 - rsGabckeCompactify γK‖ ≤
        (1 / (Real.pi * (1 + (γ - ρ) ^ 2))) * ‖γK1 - γK‖ := by
    refine (convex_Icc (γ - ρ) (γ + ρ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := rsGabckeCompactify) (f' := fun x => (1 / (1 + x ^ 2)) / Real.pi) ?_ ?_ hγK_mem hγK1_mem
    · intro x hx
      simpa [I, rsGabckeCompactify] using
        ((Real.hasDerivAt_arctan x).div_const Real.pi).hasDerivWithinAt
    · intro x hx
      have hx_nonneg : 0 ≤ x := le_trans hleft hx.1
      have hsq : (γ - ρ) ^ 2 ≤ x ^ 2 := by
        nlinarith [sq_nonneg (x - (γ - ρ)), hleft, hx.1]
      have hden :
          Real.pi * (1 + (γ - ρ) ^ 2) ≤ Real.pi * (1 + x ^ 2) := by
        nlinarith [Real.pi_pos, hsq]
      have hbase_pos : 0 < Real.pi * (1 + (γ - ρ) ^ 2) := by positivity
      have hx_pos : 0 < Real.pi * (1 + x ^ 2) := by positivity
      have hinv :
          1 / (Real.pi * (1 + x ^ 2)) ≤ 1 / (Real.pi * (1 + (γ - ρ) ^ 2)) := by
        exact one_div_le_one_div_of_le hbase_pos hden
      have hderiv_eq :
          (1 / (1 + x ^ 2)) / Real.pi = 1 / (Real.pi * (1 + x ^ 2)) := by
        have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
        have hquad_ne : 1 + x ^ 2 ≠ 0 := by positivity
        field_simp [hpi_ne, hquad_ne]
      have hnonneg : 0 ≤ (1 / (1 + x ^ 2)) / Real.pi := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hderiv_eq]
      exact hinv
  have hbound :
      |rsGabckeCompactify γK1 - rsGabckeCompactify γK| ≤
        (1 / (Real.pi * (1 + (γ - ρ) ^ 2))) * |γK1 - γK| := by
    simpa [Real.norm_eq_abs] using hdiff
  have hconst_nonneg : 0 ≤ 1 / (Real.pi * (1 + (γ - ρ) ^ 2)) := by
    positivity
  have hmul_bound :
      (1 / (Real.pi * (1 + (γ - ρ) ^ 2))) * |γK1 - γK| ≤
        (1 / (Real.pi * (1 + (γ - ρ) ^ 2))) * (|eK1 - eK| / m) := by
    exact mul_le_mul_of_nonneg_left hstep_bound hconst_nonneg
  refine le_trans hbound ?_
  refine le_trans hmul_bound ?_
  have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm_ne : m ≠ 0 := hm.ne'
  have hquad_ne : 1 + (γ - ρ) ^ 2 ≠ 0 := by positivity
  have hrewrite :
      (1 / (Real.pi * (1 + (γ - ρ) ^ 2))) * (|eK1 - eK| / m) =
        |eK1 - eK| / (Real.pi * m * (1 + (γ - ρ) ^ 2)) := by
    field_simp [hpi_ne, hm_ne, hquad_ne]
  rw [← hrewrite]

end Omega.CircleDimension
