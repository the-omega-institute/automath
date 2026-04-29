import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiIntegratedDefectGoldenAsymptotics

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Golden resolution chain `rho_m = tanh((m log phi)/2)`. -/
def xi_golden_chain_reversekl_log_barrier_rho (m : ℕ) : ℝ :=
  xi_integrated_defect_golden_asymptotics_rho m

/-- Cayley ratio attached to the golden resolution chain. -/
def xi_golden_chain_reversekl_log_barrier_cayleyRatio (m : ℕ) : ℝ :=
  (1 - xi_golden_chain_reversekl_log_barrier_rho m) /
    (1 + xi_golden_chain_reversekl_log_barrier_rho m)

/-- The logarithmic reverse-KL barrier model on a scalar Cayley ratio. -/
def xi_golden_chain_reversekl_log_barrier_kappaKL (a : ℝ) : ℝ :=
  -Real.log a - 1

/-- The linear logarithmic barrier along the golden chain. -/
def xi_golden_chain_reversekl_log_barrier_linear (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log Real.goldenRatio - 1

/-- Concrete statement for the golden-chain reverse-KL logarithmic barrier. -/
def xi_golden_chain_reversekl_log_barrier_statement : Prop :=
  (∀ m : ℕ,
    xi_golden_chain_reversekl_log_barrier_cayleyRatio m =
      1 / Real.goldenRatio ^ m) ∧
  (∀ m : ℕ,
    xi_golden_chain_reversekl_log_barrier_kappaKL (1 / Real.goldenRatio ^ m) =
      xi_golden_chain_reversekl_log_barrier_linear m) ∧
  (∀ E : ℕ → ℝ,
    Tendsto (fun m : ℕ => xi_golden_chain_reversekl_log_barrier_linear m * E m)
        atTop (nhds 0) →
      Tendsto
        (fun m : ℕ =>
          xi_golden_chain_reversekl_log_barrier_kappaKL
              (xi_golden_chain_reversekl_log_barrier_cayleyRatio m) *
            E m)
        atTop (nhds 0))

lemma xi_golden_chain_reversekl_log_barrier_cayleyRatio_eq (m : ℕ) :
    xi_golden_chain_reversekl_log_barrier_cayleyRatio m =
      1 / Real.goldenRatio ^ m := by
  have hpow_pos : 0 < (Real.goldenRatio ^ m : ℝ) := by positivity
  have hpow_ne : (Real.goldenRatio ^ m : ℝ) ≠ 0 := ne_of_gt hpow_pos
  have hden_ne : (Real.goldenRatio ^ m + 1 : ℝ) ≠ 0 := by positivity
  rw [xi_golden_chain_reversekl_log_barrier_cayleyRatio,
    xi_golden_chain_reversekl_log_barrier_rho,
    xi_integrated_defect_golden_asymptotics_rho_closed_form]
  field_simp [hpow_ne, hden_ne]
  ring

lemma xi_golden_chain_reversekl_log_barrier_kappaKL_inv_pow (m : ℕ) :
    xi_golden_chain_reversekl_log_barrier_kappaKL (1 / Real.goldenRatio ^ m) =
      xi_golden_chain_reversekl_log_barrier_linear m := by
  have hpow_pos : 0 < (Real.goldenRatio ^ m : ℝ) := by positivity
  rw [xi_golden_chain_reversekl_log_barrier_kappaKL,
    xi_golden_chain_reversekl_log_barrier_linear]
  have hlog_inv :
      Real.log (1 / Real.goldenRatio ^ m) = -Real.log (Real.goldenRatio ^ m) := by
    simp [one_div, Real.log_inv]
  rw [hlog_inv, Real.log_pow]
  ring

/-- Paper label: `cor:xi-golden-chain-reversekl-log-barrier`. -/
theorem paper_xi_golden_chain_reversekl_log_barrier :
    xi_golden_chain_reversekl_log_barrier_statement := by
  refine ⟨xi_golden_chain_reversekl_log_barrier_cayleyRatio_eq,
    xi_golden_chain_reversekl_log_barrier_kappaKL_inv_pow, ?_⟩
  intro E hE
  have hfun :
      (fun m : ℕ =>
          xi_golden_chain_reversekl_log_barrier_kappaKL
              (xi_golden_chain_reversekl_log_barrier_cayleyRatio m) *
            E m) =
        (fun m : ℕ => xi_golden_chain_reversekl_log_barrier_linear m * E m) := by
    funext m
    rw [xi_golden_chain_reversekl_log_barrier_cayleyRatio_eq,
      xi_golden_chain_reversekl_log_barrier_kappaKL_inv_pow]
  simpa [hfun] using hE

end

end Omega.Zeta
