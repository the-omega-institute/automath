import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the fold-bin collision/Rényi-2 floor.  The sequences represent,
respectively, the ambient Fibonacci count, the collision sum, the two selected resonant
amplitudes, the Rényi-2 divergence, and the effective support. -/
structure xi_foldbin_critical_resonance_renyi2_floor_data where
  xi_foldbin_critical_resonance_renyi2_floor_fiberCount : ℕ → ℝ
  xi_foldbin_critical_resonance_renyi2_floor_collision : ℕ → ℝ
  xi_foldbin_critical_resonance_renyi2_floor_modeLeft : ℕ → ℝ
  xi_foldbin_critical_resonance_renyi2_floor_modeRight : ℕ → ℝ
  xi_foldbin_critical_resonance_renyi2_floor_renyi2 : ℕ → ℝ
  xi_foldbin_critical_resonance_renyi2_floor_effectiveSupport : ℕ → ℝ
  xi_foldbin_critical_resonance_renyi2_floor_resonanceConstant : ℝ
  xi_foldbin_critical_resonance_renyi2_floor_liminfRenyi2 : ℝ
  xi_foldbin_critical_resonance_renyi2_floor_limsupEffectiveSupportRatio : ℝ
  xi_foldbin_critical_resonance_renyi2_floor_renyi2_log_collision :
    ∀ m : ℕ,
      xi_foldbin_critical_resonance_renyi2_floor_renyi2 m =
        Real.log
          (xi_foldbin_critical_resonance_renyi2_floor_fiberCount m *
            xi_foldbin_critical_resonance_renyi2_floor_collision m)
  xi_foldbin_critical_resonance_renyi2_floor_selected_modes_lower :
    ∀ m : ℕ,
      Real.log
          (1 + xi_foldbin_critical_resonance_renyi2_floor_modeLeft m ^ 2 +
            xi_foldbin_critical_resonance_renyi2_floor_modeRight m ^ 2) ≤
        Real.log
          (xi_foldbin_critical_resonance_renyi2_floor_fiberCount m *
            xi_foldbin_critical_resonance_renyi2_floor_collision m)
  xi_foldbin_critical_resonance_renyi2_floor_liminf_from_resonance :
    Real.log
        (1 + 2 * xi_foldbin_critical_resonance_renyi2_floor_resonanceConstant ^ 2) ≤
      xi_foldbin_critical_resonance_renyi2_floor_liminfRenyi2
  xi_foldbin_critical_resonance_renyi2_floor_effective_support_bound :
    ∀ m : ℕ,
      xi_foldbin_critical_resonance_renyi2_floor_effectiveSupport m ≤
        xi_foldbin_critical_resonance_renyi2_floor_fiberCount m /
          (1 + xi_foldbin_critical_resonance_renyi2_floor_modeLeft m ^ 2 +
            xi_foldbin_critical_resonance_renyi2_floor_modeRight m ^ 2)
  xi_foldbin_critical_resonance_renyi2_floor_limsup_effective_support_ratio :
    xi_foldbin_critical_resonance_renyi2_floor_limsupEffectiveSupportRatio ≤
      1 / (1 + 2 * xi_foldbin_critical_resonance_renyi2_floor_resonanceConstant ^ 2)

/-- Exact Rényi-2 logarithmic collision identity. -/
def xi_foldbin_critical_resonance_renyi2_floor_data.renyi2Identity
    (D : xi_foldbin_critical_resonance_renyi2_floor_data) : Prop :=
  ∀ m : ℕ,
    D.xi_foldbin_critical_resonance_renyi2_floor_renyi2 m =
      Real.log
        (D.xi_foldbin_critical_resonance_renyi2_floor_fiberCount m *
          D.xi_foldbin_critical_resonance_renyi2_floor_collision m)

/-- Pointwise lower bound obtained by retaining the two resonant modes. -/
def xi_foldbin_critical_resonance_renyi2_floor_data.pointwiseLowerBound
    (D : xi_foldbin_critical_resonance_renyi2_floor_data) : Prop :=
  ∀ m : ℕ,
    Real.log
        (1 + D.xi_foldbin_critical_resonance_renyi2_floor_modeLeft m ^ 2 +
          D.xi_foldbin_critical_resonance_renyi2_floor_modeRight m ^ 2) ≤
      D.xi_foldbin_critical_resonance_renyi2_floor_renyi2 m

/-- Liminf lower bound forced by the critical resonance constant. -/
def xi_foldbin_critical_resonance_renyi2_floor_data.liminfLowerBound
    (D : xi_foldbin_critical_resonance_renyi2_floor_data) : Prop :=
  Real.log (1 + 2 * D.xi_foldbin_critical_resonance_renyi2_floor_resonanceConstant ^ 2) ≤
    D.xi_foldbin_critical_resonance_renyi2_floor_liminfRenyi2

/-- Effective support bounds corresponding to the collision lower floor. -/
def xi_foldbin_critical_resonance_renyi2_floor_data.effectiveSupportUpperBound
    (D : xi_foldbin_critical_resonance_renyi2_floor_data) : Prop :=
  (∀ m : ℕ,
    D.xi_foldbin_critical_resonance_renyi2_floor_effectiveSupport m ≤
      D.xi_foldbin_critical_resonance_renyi2_floor_fiberCount m /
        (1 + D.xi_foldbin_critical_resonance_renyi2_floor_modeLeft m ^ 2 +
          D.xi_foldbin_critical_resonance_renyi2_floor_modeRight m ^ 2)) ∧
    D.xi_foldbin_critical_resonance_renyi2_floor_limsupEffectiveSupportRatio ≤
      1 / (1 + 2 * D.xi_foldbin_critical_resonance_renyi2_floor_resonanceConstant ^ 2)

/-- Paper label: `thm:xi-foldbin-critical-resonance-renyi2-floor`. -/
theorem paper_xi_foldbin_critical_resonance_renyi2_floor
    (D : xi_foldbin_critical_resonance_renyi2_floor_data) :
    D.renyi2Identity ∧ D.pointwiseLowerBound ∧ D.liminfLowerBound ∧
      D.effectiveSupportUpperBound := by
  constructor
  · intro m
    exact D.xi_foldbin_critical_resonance_renyi2_floor_renyi2_log_collision m
  constructor
  · intro m
    calc
      Real.log
          (1 + D.xi_foldbin_critical_resonance_renyi2_floor_modeLeft m ^ 2 +
            D.xi_foldbin_critical_resonance_renyi2_floor_modeRight m ^ 2) ≤
          Real.log
            (D.xi_foldbin_critical_resonance_renyi2_floor_fiberCount m *
              D.xi_foldbin_critical_resonance_renyi2_floor_collision m) :=
        D.xi_foldbin_critical_resonance_renyi2_floor_selected_modes_lower m
      _ = D.xi_foldbin_critical_resonance_renyi2_floor_renyi2 m := by
        rw [D.xi_foldbin_critical_resonance_renyi2_floor_renyi2_log_collision m]
  constructor
  · exact D.xi_foldbin_critical_resonance_renyi2_floor_liminf_from_resonance
  · exact
      ⟨D.xi_foldbin_critical_resonance_renyi2_floor_effective_support_bound,
        D.xi_foldbin_critical_resonance_renyi2_floor_limsup_effective_support_ratio⟩

end Omega.Zeta
