import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9odEscortEscortFdivBinaryClosure

namespace Omega.Zeta

noncomputable section

/-- The limiting Rényi divergence of the two-block escort closure. -/
def xi_foldbin_escort_renyi_kl_two_point_closure_renyi_limit
    (α : ℝ) (q r : ℕ) : ℝ :=
  Real.log (xiEscortBinaryFDivLimit (fun u : ℝ => u ^ α) r q) / (α - 1)

/-- The explicit Bernoulli two-point Rényi expression in the escort parameter `θ(q)`. -/
def xi_foldbin_escort_renyi_kl_two_point_closure_renyi_two_point
    (α : ℝ) (q r : ℕ) : ℝ :=
  Real.log
      ((1 - xiEscortTheta q) ^ α * (1 - xiEscortTheta r) ^ (1 - α) +
        xiEscortTheta q ^ α * xiEscortTheta r ^ (1 - α)) /
    (α - 1)

/-- The limiting KL divergence in the two-block escort closure. -/
def xi_foldbin_escort_renyi_kl_two_point_closure_kl_limit (q r : ℕ) : ℝ :=
  xiEscortBinaryKLLimit r q

/-- The closed Bernoulli KL form determined by the escort parameter `θ(q)`. -/
def xi_foldbin_escort_renyi_kl_two_point_closure_kl_two_point (q r : ℕ) : ℝ :=
  (1 - xiEscortTheta q) * Real.log ((1 - xiEscortTheta q) / (1 - xiEscortTheta r)) +
    xiEscortTheta q * Real.log (xiEscortTheta q / xiEscortTheta r)

/-- Concrete two-point closure statement for escort Rényi and KL limits. -/
def xi_foldbin_escort_renyi_kl_two_point_closure_statement
    (α : ℝ) (q r : ℕ) : Prop :=
  0 < α →
    α ≠ 1 →
      xi_foldbin_escort_renyi_kl_two_point_closure_renyi_limit α q r =
          xi_foldbin_escort_renyi_kl_two_point_closure_renyi_two_point α q r ∧
        xi_foldbin_escort_renyi_kl_two_point_closure_kl_limit q r =
          xi_foldbin_escort_renyi_kl_two_point_closure_kl_two_point q r

/-- Paper label: `thm:xi-foldbin-escort-renyi-kl-two-point-closure`. -/
theorem paper_xi_foldbin_escort_renyi_kl_two_point_closure (α : ℝ) (q r : ℕ) :
    xi_foldbin_escort_renyi_kl_two_point_closure_statement α q r := by
  intro _hα hα_ne
  refine ⟨?_, ?_⟩
  · exact xiEscortBinaryRenyiClosedForm α r q
  · simp [xi_foldbin_escort_renyi_kl_two_point_closure_kl_limit,
      xi_foldbin_escort_renyi_kl_two_point_closure_kl_two_point,
      xiEscortBinaryKLLimit, add_comm]

end

end Omega.Zeta
