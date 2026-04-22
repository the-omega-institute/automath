import Mathlib

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Finite disk-zero package for the Jensen power-law counting identity. -/
structure app_jensen_zero_count_power_law_data where
  zeros : Multiset ℂ
  m : ℕ

namespace app_jensen_zero_count_power_law_data

/-- The `m`-fold power pullback zero multiset adjoining `m` copies above each original zero. -/
def pullbackZeros (D : app_jensen_zero_count_power_law_data) : Multiset ℂ :=
  D.zeros.bind fun z => Multiset.replicate D.m z

/-- The pullback zero count scales by the degree of the power map. -/
def statement (D : app_jensen_zero_count_power_law_data) : Prop :=
  D.pullbackZeros.card = D.m * D.zeros.card

end app_jensen_zero_count_power_law_data

/-- Paper label: `cor:app-jensen-zero-count-power-law`. Each original disk zero contributes
exactly `m` pullback roots, so the power-pullback multiset has cardinality `m` times the original
zero count. -/
theorem paper_app_jensen_zero_count_power_law (D : app_jensen_zero_count_power_law_data) :
    D.statement := by
  rw [app_jensen_zero_count_power_law_data.statement,
    app_jensen_zero_count_power_law_data.pullbackZeros, Multiset.card_bind]
  simp [Nat.mul_comm]

end

end Omega.UnitCirclePhaseArithmetic
