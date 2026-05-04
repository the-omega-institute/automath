import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanAnchorDetCauchyVandermonde

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Real-axis charge term in the full-rank anchor balance equation. -/
def xi_basepoint_scan_full_rank_anchor_critical_equations_realCharge {κ : ℕ}
    (x : Fin κ → ℝ) (i : Fin κ) : ℝ :=
  ∑ j : Fin κ, if j = i then 0 else 1 / (x i - x j)

/-- Complex-pole contribution after taking real parts. -/
def xi_basepoint_scan_full_rank_anchor_critical_equations_poleCharge {κ : ℕ}
    (x γ a : Fin κ → ℝ) (i : Fin κ) : ℝ :=
  ∑ k : Fin κ, (x i - γ k) / ((x i - γ k) ^ (2 : ℕ) + a k ^ (2 : ℕ))

/-- Log-determinant gradient for the Cauchy--Vandermonde full-rank anchor determinant. -/
def xi_basepoint_scan_full_rank_anchor_critical_equations_logGradient {κ : ℕ}
    (x γ a : Fin κ → ℝ) (i : Fin κ) : ℝ :=
  2 *
    (xi_basepoint_scan_full_rank_anchor_critical_equations_realCharge x i -
      xi_basepoint_scan_full_rank_anchor_critical_equations_poleCharge x γ a i)

/-- The displayed full-rank anchor critical equations. -/
def xi_basepoint_scan_full_rank_anchor_critical_equations_balance {κ : ℕ}
    (x γ a : Fin κ → ℝ) : Prop :=
  ∀ i : Fin κ,
    xi_basepoint_scan_full_rank_anchor_critical_equations_realCharge x i =
      xi_basepoint_scan_full_rank_anchor_critical_equations_poleCharge x γ a i

/-- Concrete statement for `prop:xi-basepoint-scan-full-rank-anchor-critical-equations`. -/
def xi_basepoint_scan_full_rank_anchor_critical_equations_statement : Prop :=
  (∀ κ n : ℕ, ∀ D : XiBasepointAnchorData κ n, D.anchorDetCauchyVandermondeClosedForm) ∧
    ∀ κ : ℕ, ∀ x γ a : Fin κ → ℝ,
      (∀ i : Fin κ,
        xi_basepoint_scan_full_rank_anchor_critical_equations_logGradient x γ a i = 0) →
      xi_basepoint_scan_full_rank_anchor_critical_equations_balance x γ a

lemma xi_basepoint_scan_full_rank_anchor_critical_equations_balance_of_gradient {κ : ℕ}
    (x γ a : Fin κ → ℝ)
    (hgrad : ∀ i : Fin κ,
      xi_basepoint_scan_full_rank_anchor_critical_equations_logGradient x γ a i = 0) :
    xi_basepoint_scan_full_rank_anchor_critical_equations_balance x γ a := by
  intro i
  have hi := hgrad i
  unfold xi_basepoint_scan_full_rank_anchor_critical_equations_logGradient at hi
  linarith

/-- Paper label: `prop:xi-basepoint-scan-full-rank-anchor-critical-equations`. -/
theorem paper_xi_basepoint_scan_full_rank_anchor_critical_equations :
    xi_basepoint_scan_full_rank_anchor_critical_equations_statement := by
  refine ⟨?_, ?_⟩
  · intro κ n D
    exact paper_xi_basepoint_scan_anchor_det_cauchy_vandermonde D
  · intro κ x γ a hgrad
    exact xi_basepoint_scan_full_rank_anchor_critical_equations_balance_of_gradient x γ a hgrad

end

end Omega.Zeta
