import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Concrete audit data for the golden-chain Poisson--KL alignment rate. The fields record the
defect, the Poisson--KL proxy, the residual error, the resolution scale, and the two inequalities
used in the paper argument. -/
structure xi_golden_chain_poisson_kl_alignment_rate_data where
  xi_golden_chain_poisson_kl_alignment_rate_defect : ℕ → ℝ
  xi_golden_chain_poisson_kl_alignment_rate_klProxy : ℕ → ℝ
  xi_golden_chain_poisson_kl_alignment_rate_epsilon : ℕ → ℝ
  xi_golden_chain_poisson_kl_alignment_rate_constant : ℝ
  xi_golden_chain_poisson_kl_alignment_rate_time : ℕ → ℝ
  xi_golden_chain_poisson_kl_alignment_rate_time_eq_golden :
    ∀ m : ℕ, xi_golden_chain_poisson_kl_alignment_rate_time m = Real.goldenRatio ^ m
  xi_golden_chain_poisson_kl_alignment_rate_alignment :
    ∀ m : ℕ,
      xi_golden_chain_poisson_kl_alignment_rate_defect m ≤
        xi_golden_chain_poisson_kl_alignment_rate_klProxy m +
          xi_golden_chain_poisson_kl_alignment_rate_epsilon m
  xi_golden_chain_poisson_kl_alignment_rate_kl_asymptotic :
    ∀ m : ℕ,
      xi_golden_chain_poisson_kl_alignment_rate_klProxy m ≤
        xi_golden_chain_poisson_kl_alignment_rate_constant /
          xi_golden_chain_poisson_kl_alignment_rate_time m
  xi_golden_chain_poisson_kl_alignment_rate_epsilon_decay :
    Tendsto xi_golden_chain_poisson_kl_alignment_rate_epsilon atTop (nhds 0)

/-- The uniform golden-chain defect certificate obtained after rewriting `t_m = phi^m`. -/
def xi_golden_chain_poisson_kl_alignment_rate_rateBound
    (D : xi_golden_chain_poisson_kl_alignment_rate_data) (m : ℕ) : Prop :=
  D.xi_golden_chain_poisson_kl_alignment_rate_defect m ≤
    D.xi_golden_chain_poisson_kl_alignment_rate_constant / Real.goldenRatio ^ m +
      D.xi_golden_chain_poisson_kl_alignment_rate_epsilon m

/-- Paper-facing statement: the aligned defect has the uniform `phi^{-m}` KL rate, with the
recorded residual tending to zero. -/
def xi_golden_chain_poisson_kl_alignment_rate_statement
    (D : xi_golden_chain_poisson_kl_alignment_rate_data) : Prop :=
  (∀ m : ℕ, xi_golden_chain_poisson_kl_alignment_rate_rateBound D m) ∧
    Tendsto D.xi_golden_chain_poisson_kl_alignment_rate_epsilon atTop (nhds 0)

/-- Paper label: `prop:xi-golden-chain-poisson-kl-alignment-rate`. -/
theorem paper_xi_golden_chain_poisson_kl_alignment_rate
    (D : xi_golden_chain_poisson_kl_alignment_rate_data) :
    xi_golden_chain_poisson_kl_alignment_rate_statement D := by
  refine ⟨?_, D.xi_golden_chain_poisson_kl_alignment_rate_epsilon_decay⟩
  intro m
  rw [xi_golden_chain_poisson_kl_alignment_rate_rateBound]
  have hkl := D.xi_golden_chain_poisson_kl_alignment_rate_kl_asymptotic m
  rw [D.xi_golden_chain_poisson_kl_alignment_rate_time_eq_golden m] at hkl
  have halign := D.xi_golden_chain_poisson_kl_alignment_rate_alignment m
  nlinarith

end

end Omega.Zeta
