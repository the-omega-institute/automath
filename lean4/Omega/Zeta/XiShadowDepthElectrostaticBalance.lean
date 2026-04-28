import Mathlib.Tactic
import Omega.Zeta.XiShadowSpectrumInterlacing

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Finite Stieltjes sum `S(t) = Σ w_j / (t + a_j)`. -/
def xi_shadow_depth_electrostatic_balance_stieltjes_sum
    (k : ℕ) (depth weight : Fin (k + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin (k + 1), weight j / (t + depth j)

/-- Electrostatic balance sum obtained after substituting `t = -b`. -/
def xi_shadow_depth_electrostatic_balance_electrostatic_sum
    (k : ℕ) (depth weight : Fin (k + 1) → ℝ) (b : ℝ) : ℝ :=
  ∑ j : Fin (k + 1), weight j / (depth j - b)

/-- The open interval between adjacent true depths for the `m`th shadow point. -/
def xi_shadow_depth_electrostatic_balance_in_shadow_interval
    (k : ℕ) (depth : Fin (k + 1) → ℝ) (m : Fin k) (b : ℝ) : Prop :=
  depth m.castSucc < b ∧ b < depth m.succ

/-- Substituting `t = -b` rewrites the Stieltjes zero equation as electrostatic balance. -/
lemma xi_shadow_depth_electrostatic_balance_stieltjes_substitution
    (k : ℕ) (depth weight : Fin (k + 1) → ℝ) (b : ℝ) :
    xi_shadow_depth_electrostatic_balance_stieltjes_sum k depth weight (-b) =
      xi_shadow_depth_electrostatic_balance_electrostatic_sum k depth weight b := by
  unfold xi_shadow_depth_electrostatic_balance_stieltjes_sum
    xi_shadow_depth_electrostatic_balance_electrostatic_sum
  refine Finset.sum_congr rfl ?_
  intro j _hj
  have hden : -b + depth j = depth j - b := by
    ring
  rw [hden]

/-- Paper-facing conclusion for the finite shadow-depth balance package. -/
def xi_shadow_depth_electrostatic_balance_statement
    (k : ℕ) (depth weight : Fin (k + 1) → ℝ) (shadow : Fin k → ℝ)
    (interlacingData : xi_shadow_spectrum_tower_principal_minors_data) : Prop :=
  interlacingData.statement ∧
    (∀ m : Fin k, xi_shadow_depth_electrostatic_balance_in_shadow_interval k depth m (shadow m)) ∧
    (∀ m : Fin k,
      xi_shadow_depth_electrostatic_balance_electrostatic_sum k depth weight (shadow m) = 0) ∧
    (∀ (m : Fin k) (b : ℝ),
      xi_shadow_depth_electrostatic_balance_in_shadow_interval k depth m b →
        xi_shadow_depth_electrostatic_balance_electrostatic_sum k depth weight b = 0 →
          b = shadow m)

/-- Paper label: `cor:xi-shadow-depth-electrostatic-balance`. -/
theorem paper_xi_shadow_depth_electrostatic_balance
    (k : ℕ) (depth weight : Fin (k + 1) → ℝ) (shadow : Fin k → ℝ)
    (interlacingData : xi_shadow_spectrum_tower_principal_minors_data)
    (xi_shadow_depth_electrostatic_balance_shadow_interval :
      ∀ m : Fin k, xi_shadow_depth_electrostatic_balance_in_shadow_interval k depth m (shadow m))
    (xi_shadow_depth_electrostatic_balance_shadow_stieltjes_zero :
      ∀ m : Fin k,
        xi_shadow_depth_electrostatic_balance_stieltjes_sum k depth weight (-(shadow m)) = 0)
    (xi_shadow_depth_electrostatic_balance_stieltjes_zero_unique :
      ∀ (m : Fin k) (b : ℝ),
        xi_shadow_depth_electrostatic_balance_in_shadow_interval k depth m b →
          xi_shadow_depth_electrostatic_balance_stieltjes_sum k depth weight (-b) = 0 →
            b = shadow m) :
    xi_shadow_depth_electrostatic_balance_statement k depth weight shadow interlacingData := by
  refine ⟨paper_xi_shadow_spectrum_interlacing interlacingData,
    xi_shadow_depth_electrostatic_balance_shadow_interval, ?_, ?_⟩
  · intro m
    have hS :
        xi_shadow_depth_electrostatic_balance_stieltjes_sum k depth weight (-(shadow m)) =
          0 := xi_shadow_depth_electrostatic_balance_shadow_stieltjes_zero m
    simpa [xi_shadow_depth_electrostatic_balance_stieltjes_substitution] using hS
  · intro m b hb hbalance
    have hS : xi_shadow_depth_electrostatic_balance_stieltjes_sum k depth weight (-b) = 0 := by
      simpa [xi_shadow_depth_electrostatic_balance_stieltjes_substitution] using hbalance
    exact xi_shadow_depth_electrostatic_balance_stieltjes_zero_unique m b hb hS

end

end Omega.Zeta
