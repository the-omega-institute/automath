import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete two-base residue-ratio recovery data. The ratio code is evaluated at two real bases
`b₁,b₂ > 1`, and the irrationality of `log b₁ / log b₂` rules out a nontrivial common period. -/
structure TwoBaseResidueRatioRecoveryData where
  b1 : ℝ
  b2 : ℝ
  hb1 : 1 < b1
  hb2 : 1 < b2
  rho : ℂ
  rho' : ℂ
  hlogRatioIrr :
    Irrational (Real.log b1 / Real.log b2)

namespace TwoBaseResidueRatioRecoveryData

/-- The residue-ratio code at the positive base `b`. -/
noncomputable def residueRatio (b : ℝ) (ρ : ℂ) : ℂ :=
  Complex.exp (-(ρ - (1 / 2 : ℂ)) * Real.log b)

/-- Equality of the residue-ratio codes at `b₁`. -/
def sameCodeBase1 (D : TwoBaseResidueRatioRecoveryData) : Prop :=
  residueRatio D.b1 D.rho = residueRatio D.b1 D.rho'

/-- Equality of the residue-ratio codes at `b₂`. -/
def sameCodeBase2 (D : TwoBaseResidueRatioRecoveryData) : Prop :=
  residueRatio D.b2 D.rho = residueRatio D.b2 D.rho'

end TwoBaseResidueRatioRecoveryData

open TwoBaseResidueRatioRecoveryData

/-- The two residue-ratio codes at incommensurable logarithmic bases uniquely recover the zero.
    thm:xi-two-base-residue-ratio-unique-recovery -/
theorem paper_xi_two_base_residue_ratio_unique_recovery (D : TwoBaseResidueRatioRecoveryData) :
    D.sameCodeBase1 → D.sameCodeBase2 → D.rho = D.rho' := by
  intro hbase1 hbase2
  let Δ : ℂ := D.rho - D.rho'
  have hb1_log_pos : 0 < Real.log D.b1 := Real.log_pos D.hb1
  have hb2_log_pos : 0 < Real.log D.b2 := Real.log_pos D.hb2
  have hb1_log_ne : Real.log D.b1 ≠ 0 := hb1_log_pos.ne'
  have hb2_log_ne : Real.log D.b2 ≠ 0 := hb2_log_pos.ne'
  rcases (Complex.exp_eq_exp_iff_exists_int.mp hbase1) with ⟨m, hm⟩
  rcases (Complex.exp_eq_exp_iff_exists_int.mp hbase2) with ⟨n, hn⟩
  have hm_shift :=
    congrArg (fun z : ℂ => z + (D.rho' - (1 / 2 : ℂ)) * Real.log D.b1) hm
  have hn_shift :=
    congrArg (fun z : ℂ => z + (D.rho' - (1 / 2 : ℂ)) * Real.log D.b2) hn
  have hm_delta : -Δ * Real.log D.b1 = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    simpa [Δ, TwoBaseResidueRatioRecoveryData.sameCodeBase1,
      TwoBaseResidueRatioRecoveryData.residueRatio, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hm_shift
  have hn_delta : -Δ * Real.log D.b2 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    simpa [Δ, TwoBaseResidueRatioRecoveryData.sameCodeBase2,
      TwoBaseResidueRatioRecoveryData.residueRatio, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hn_shift
  have hm_parts := Complex.ext_iff.mp hm_delta
  have hn_parts := Complex.ext_iff.mp hn_delta
  have hΔre_b1 : Δ.re * Real.log D.b1 = 0 := by
    have h : -(Δ.re * Real.log D.b1) = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hm_parts.1
    linarith
  have hΔre : Δ.re = 0 := by
    have h : Δ.re * Real.log D.b1 = 0 * Real.log D.b1 := by simpa using hΔre_b1
    exact mul_right_cancel₀ hb1_log_ne h
  have hm_period : Δ.im * Real.log D.b1 = -(m : ℝ) * (2 * Real.pi) := by
    have h : -(Δ.im * Real.log D.b1) = (m : ℝ) * (2 * Real.pi) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hm_parts.2
    linarith
  have hn_period : Δ.im * Real.log D.b2 = -(n : ℝ) * (2 * Real.pi) := by
    have h : -(Δ.im * Real.log D.b2) = (n : ℝ) * (2 * Real.pi) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hn_parts.2
    linarith
  by_cases hΔim : Δ.im = 0
  · have hΔzero : Δ = 0 := by
      apply Complex.ext <;> simp [hΔre, hΔim]
    exact sub_eq_zero.mp <| by simpa [Δ] using hΔzero
  · have hm_ne : m ≠ 0 := by
      intro hm0
      have hm0_real : (m : ℝ) = 0 := by exact_mod_cast hm0
      have : Δ.im * Real.log D.b1 = 0 := by simpa [hm0_real] using hm_period
      have hΔim_zero : Δ.im = 0 := mul_right_cancel₀ hb1_log_ne <| by simpa using this
      exact hΔim hΔim_zero
    have hn_ne : n ≠ 0 := by
      intro hn0
      have hn0_real : (n : ℝ) = 0 := by exact_mod_cast hn0
      have : Δ.im * Real.log D.b2 = 0 := by simpa [hn0_real] using hn_period
      have hΔim_zero : Δ.im = 0 := mul_right_cancel₀ hb2_log_ne <| by simpa using this
      exact hΔim hΔim_zero
    have hn_real_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_ne
    have htwoPi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hcross : (m : ℝ) * Real.log D.b2 = (n : ℝ) * Real.log D.b1 := by
      have h1 := congrArg (fun x : ℝ => x * Real.log D.b2) hm_period
      have h2 := congrArg (fun x : ℝ => x * Real.log D.b1) hn_period
      have hscaled :
          ((m : ℝ) * Real.log D.b2) * (2 * Real.pi) =
            ((n : ℝ) * Real.log D.b1) * (2 * Real.pi) := by
        nlinarith [h1, h2]
      exact mul_right_cancel₀ htwoPi_ne <| by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hratio : Real.log D.b1 / Real.log D.b2 = (m : ℝ) / (n : ℝ) := by
      field_simp [hb2_log_ne, hn_real_ne]
      nlinarith [hcross]
    exact False.elim <|
      ((irrational_iff_ne_rational _).mp D.hlogRatioIrr m n hn_ne) <| by
        simpa using hratio

end Omega.Zeta
