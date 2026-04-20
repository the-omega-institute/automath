import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicTwoStateSFT
import Omega.Kronecker.MetallicGap

namespace Omega.Zeta

open Omega.Folding

/-- Entropy rate per unit symbol budget for the constant-type metallic branch. -/
noncomputable def metallicEntropyRate (A : Nat) : ℝ :=
  Real.log (metallicPerronRoot (A : ℝ)) / (A : ℝ)

private lemma metallicPerronRoot_nat_gt_one {A : Nat} (hA : 1 ≤ A) :
    1 < metallicPerronRoot (A : ℝ) := by
  have hA_real : (1 : ℝ) ≤ A := by
    exact_mod_cast hA
  have hsq : (2 : ℝ) ^ 2 < (A : ℝ) ^ 2 + 4 := by
    nlinarith [sq_nonneg ((A : ℝ) - 1)]
  have hsqrt : 2 < Real.sqrt ((A : ℝ) ^ 2 + 4) := by
    have : Real.sqrt ((2 : ℝ) ^ 2) < Real.sqrt ((A : ℝ) ^ 2 + 4) := by
      exact Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) hsq
    simpa using this
  rw [metallicPerronRoot]
  nlinarith

/-- The constant-type metallic branch has entropy rate `log λ_A / A`, where `λ_A` is the Perron
root of `X^2 - A X - 1`; the rate is strictly maximized at the golden case `A = 1`.
    thm:xi-golden-metallic-symbol-budget-entropy-optimality -/
theorem paper_xi_golden_metallic_symbol_budget_entropy_optimality (A : Nat) (hA : 1 ≤ A) :
    metallicEntropyRate A =
        Real.log (((A : ℝ) + Real.sqrt ((A : ℝ)^2 + 4)) / 2) / (A : ℝ) ∧
      (2 ≤ A → metallicEntropyRate A < Real.log ((1 + Real.sqrt 5) / 2)) := by
  constructor
  · simp [metallicEntropyRate, metallicPerronRoot]
  · intro hA2
    have hphi : metallicPerronRoot (1 : ℝ) = Real.goldenRatio := by
      rw [metallicPerronRoot, Real.goldenRatio]
      norm_num
    have hA_real : (1 : ℝ) < A := by
      exact_mod_cast hA2
    have h1_mem : (1 : ℝ) ∈ Set.Ici 1 := by simp
    have hA_mem : (A : ℝ) ∈ Set.Ici 1 := by
      show (1 : ℝ) ≤ A
      exact_mod_cast hA
    have hgap :
        1 / Real.log (metallicPerronRoot (1 : ℝ)) <
          (A : ℝ) / Real.log (metallicPerronRoot (A : ℝ)) := by
      simpa using Omega.Kronecker.paper_kronecker_metallic_gap h1_mem hA_mem hA_real
    have hlog_phi_pos : 0 < Real.log (metallicPerronRoot (1 : ℝ)) := by
      rw [hphi]
      exact Real.log_pos Real.one_lt_goldenRatio
    have hlogA_pos : 0 < Real.log (metallicPerronRoot (A : ℝ)) := by
      exact Real.log_pos (metallicPerronRoot_nat_gt_one hA)
    have hlog_phi_ne : Real.log (metallicPerronRoot (1 : ℝ)) ≠ 0 := ne_of_gt hlog_phi_pos
    have hlogA_ne : Real.log (metallicPerronRoot (A : ℝ)) ≠ 0 := ne_of_gt hlogA_pos
    have hcross :
        Real.log (metallicPerronRoot (A : ℝ)) <
          (A : ℝ) * Real.log (metallicPerronRoot (1 : ℝ)) := by
      have htmp := hgap
      field_simp [hlog_phi_ne, hlogA_ne] at htmp
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
    have hA_pos : (0 : ℝ) < A := by
      exact_mod_cast hA
    have hfinal :
        Real.log (metallicPerronRoot (A : ℝ)) / (A : ℝ) <
          Real.log (metallicPerronRoot (1 : ℝ)) := by
      exact (_root_.div_lt_iff₀ hA_pos).2 <| by simpa [mul_comm] using hcross
    rw [hphi] at hfinal
    simpa [metallicEntropyRate, metallicPerronRoot, Real.goldenRatio] using hfinal

end Omega.Zeta
