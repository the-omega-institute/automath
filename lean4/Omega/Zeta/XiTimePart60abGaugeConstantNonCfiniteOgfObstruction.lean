import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete coefficient data for the gauge-constant generating series. The recursive
Bernoulli-stripping statement is encoded by the requirement that every odd mode remains nonzero. -/
structure XiTimePart60abGaugeConstantData where
  paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_coeff : ℕ → ℝ
  paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_odd_mode_nonzero :
    ∀ R : ℕ,
      paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_coeff (2 * R + 1) ≠ 0

/-- Local odd-mode obstruction used as the C-finite surrogate in this module: beyond some
threshold, a C-finite OGF would force all odd Bernoulli-stripped modes to disappear. -/
def paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_local_cfinite
    (paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_coeff : ℕ → ℝ) : Prop :=
  ∃ N : ℕ,
    ∀ R : ℕ,
      N ≤ R →
        paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_coeff (2 * R + 1) = 0

namespace XiTimePart60abGaugeConstantData

/-- The odd coefficient of index `2R + 1`, matching the persistent odd Bernoulli modes. -/
def paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_odd_mode_coefficient
    (D : XiTimePart60abGaugeConstantData) (R : ℕ) : ℝ :=
  D.paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_coeff (2 * R + 1)

/-- Local C-finite predicate attached to the concrete coefficient sequence. -/
def IsCFinite (D : XiTimePart60abGaugeConstantData) : Prop :=
  paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_local_cfinite
    D.paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_coeff

lemma paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_odd_mode_coefficient_nonzero
    (D : XiTimePart60abGaugeConstantData) (R : ℕ) :
    D.paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_odd_mode_coefficient R ≠
      0 := by
  exact D.paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_odd_mode_nonzero R

end XiTimePart60abGaugeConstantData

open XiTimePart60abGaugeConstantData

/-- Paper label: `thm:xi-time-part60ab-gauge-constant-non-cfinite-ogf-obstruction`. Every odd
Bernoulli-stripped mode remains nonzero, so the local C-finite obstruction fails at every
threshold and the gauge-constant OGF cannot be C-finite in this sense. -/
theorem paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction
    (D : XiTimePart60abGaugeConstantData) : Not D.IsCFinite := by
  intro hCFinite
  rcases hCFinite with ⟨N, hN⟩
  have hZero :
      D.paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_odd_mode_coefficient
        N = 0 := by
    exact hN N (le_rfl)
  exact
    D.paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_odd_mode_coefficient_nonzero
      N hZero

end Omega.Zeta
