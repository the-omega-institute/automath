import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.RadialInformationProjectionLowerBound
import Omega.UnitCirclePhaseArithmetic.UnitCirclePhaseLogConditionNumbers

namespace Omega.CircleDimension

open Omega.TypedAddressBiaxialCompletion

/-- The precision-potential argument controlling dyadic code length. -/
noncomputable def precisionPotentialArgument (x ε : ℝ) : ℝ :=
  Real.exp (Omega.UnitCirclePhaseArithmetic.phasePrecisionPotential x) / ε

/-- An explicit dyadic prefix length obtained by rounding the precision potential up to the next
bit and adding one safety bit. -/
noncomputable def explicitDyadicPrefixLength (x ε : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (precisionPotentialArgument x ε)) + 1

theorem precisionPotentialArgument_eq (x ε : ℝ) :
    precisionPotentialArgument x ε = xiJacobianAmplification x / ε := by
  unfold precisionPotentialArgument
  rw [Omega.UnitCirclePhaseArithmetic.phasePrecisionPotential, xiJacobianAmplification]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hone : 0 < 1 + x ^ 2 := by positivity
  calc
    Real.exp (Real.log Real.pi + Real.log (1 + x ^ 2)) / ε
        = (Real.exp (Real.log Real.pi) * Real.exp (Real.log (1 + x ^ 2))) / ε := by
            rw [Real.exp_add]
    _ = (Real.pi * (1 + x ^ 2)) / ε := by rw [Real.exp_log hpi, Real.exp_log hone]
    _ = xiJacobianAmplification x / ε := by simp [xiJacobianAmplification]

/-- Paper-facing optimality wrapper for `u(x) = arctan(x) / π`: any certified `δ`-accurate dyadic
phase code must respect the Jacobian lower bound, while the explicit ceiling construction yields a
matching dyadic width up to an additive constant. -/
theorem paper_cdim_precision_potential_delta_coding_optimality
    (x ε : ℝ) (n : ℕ)
    (hε : 0 < ε)
    (hscale : ε ≤ xiJacobianAmplification x)
    (hcert : xiCertifiedRadialReadout x ε n) :
    xiCompactify x = Real.arctan x / Real.pi ∧
      Omega.UnitCirclePhaseArithmetic.phasePrecisionPotential x =
        Real.log Real.pi + Real.log (1 + x ^ 2) ∧
      Real.logb 2 (precisionPotentialArgument x ε) ≤ n ∧
      let m := explicitDyadicPrefixLength x ε
      xiDyadicWidth m ≤ ε / xiJacobianAmplification x ∧
        (m : ℝ) ≤ Real.logb 2 (precisionPotentialArgument x ε) + 2 := by
  have harg_eq : precisionPotentialArgument x ε = xiJacobianAmplification x / ε :=
    precisionPotentialArgument_eq x ε
  have hJpos : 0 < xiJacobianAmplification x := xiJacobianAmplification_pos x
  have harg_pos : 0 < precisionPotentialArgument x ε := by
    rw [harg_eq]
    exact div_pos hJpos hε
  have hlog_nonneg : 0 ≤ Real.logb 2 (precisionPotentialArgument x ε) := by
    have hone_le : (1 : ℝ) ≤ precisionPotentialArgument x ε := by
      rw [harg_eq]
      exact (one_le_div hε).2 hscale
    exact Real.logb_nonneg (by norm_num) hone_le
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simpa [harg_eq] using paper_xi_radial_information_projection_lower_bound x ε n hε hcert
  · dsimp [explicitDyadicPrefixLength]
    let m := Nat.ceil (Real.logb 2 (precisionPotentialArgument x ε)) + 1
    have hlog_le_ceil : Real.logb 2 (precisionPotentialArgument x ε) ≤ Nat.ceil
        (Real.logb 2 (precisionPotentialArgument x ε)) := by
      exact Nat.le_ceil _
    have hlog_le_m : Real.logb 2 (precisionPotentialArgument x ε) ≤ m := by
      dsimp [m]
      exact le_trans hlog_le_ceil (by exact_mod_cast Nat.le_succ _)
    have harg_le_pow : precisionPotentialArgument x ε ≤ (2 : ℝ) ^ m := by
      have htmp :=
        (Real.logb_le_iff_le_rpow (b := (2 : ℝ)) (hb := by norm_num) harg_pos).1 hlog_le_m
      simpa [Real.rpow_natCast] using htmp
    have hwidth_aux : xiDyadicWidth m ≤ (precisionPotentialArgument x ε)⁻¹ := by
      dsimp [xiDyadicWidth]
      simpa [one_div] using (one_div_le_one_div_of_le harg_pos harg_le_pow)
    have hwidth :
        xiDyadicWidth m ≤ ε / xiJacobianAmplification x := by
      rw [harg_eq] at hwidth_aux
      have hrewrite : (xiJacobianAmplification x / ε)⁻¹ = ε / xiJacobianAmplification x := by
        field_simp [hε.ne', hJpos.ne']
      simpa [hrewrite] using hwidth_aux
    have hm_le :
        (m : ℝ) ≤ Real.logb 2 (precisionPotentialArgument x ε) + 2 := by
      have hceil_le :
          (Nat.ceil (Real.logb 2 (precisionPotentialArgument x ε)) : ℝ) ≤
            Real.logb 2 (precisionPotentialArgument x ε) + 1 := by
        exact (Nat.ceil_lt_add_one hlog_nonneg).le
      calc
        (m : ℝ) = (Nat.ceil (Real.logb 2 (precisionPotentialArgument x ε)) : ℝ) + 1 := by
          dsimp [m]
          norm_num
        _ ≤ Real.logb 2 (precisionPotentialArgument x ε) + 2 := by
          linarith
    exact ⟨hwidth, hm_le⟩

end Omega.CircleDimension
