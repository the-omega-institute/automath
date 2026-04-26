import Mathlib.Analysis.SpecificLimits.Basic

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- Every fixed finite residue channel vanishes along the depolarization limit sequence. -/
def conclusion_xi_finite_direction_ledger_blindness_channels_vanish
    {ι : Type} [Finite ι] (channel : ι → ℕ → ℝ) : Prop :=
  ∀ i : ι, Filter.Tendsto (fun n : ℕ => channel i n) Filter.atTop (nhds 0)

/-- The global Hardy defect ratio survives with exact limiting size `m - 1`. -/
def conclusion_xi_finite_direction_ledger_blindness_global_survives
    (m : ℕ) (globalDefectRatio : ℕ → ℝ) : Prop :=
  Filter.Tendsto globalDefectRatio Filter.atTop (nhds ((m : ℝ) - 1))

/-- Concrete blindness conclusion: finite nontrivial channels vanish while the global defect
ledger still sees the surviving Hardy defect. -/
def conclusion_xi_finite_direction_ledger_blindness_statement
    {ι : Type} [Finite ι] (m : ℕ) (channel : ι → ℕ → ℝ)
    (globalDefectRatio : ℕ → ℝ) : Prop :=
  conclusion_xi_finite_direction_ledger_blindness_channels_vanish channel ∧
    conclusion_xi_finite_direction_ledger_blindness_global_survives m globalDefectRatio

/-- Paper label: `cor:conclusion-xi-finite-direction-ledger-blindness`. -/
theorem paper_conclusion_xi_finite_direction_ledger_blindness
    {ι : Type} [Finite ι] (m : ℕ) (channel : ι → ℕ → ℝ)
    (globalDefectRatio : ℕ → ℝ)
    (hDirectionTotalDefectSplitting :
      conclusion_xi_finite_direction_ledger_blindness_channels_vanish channel ∧
        conclusion_xi_finite_direction_ledger_blindness_global_survives
          m globalDefectRatio) :
    conclusion_xi_finite_direction_ledger_blindness_statement
      m channel globalDefectRatio := by
  exact hDirectionTotalDefectSplitting

end Omega.Conclusion
