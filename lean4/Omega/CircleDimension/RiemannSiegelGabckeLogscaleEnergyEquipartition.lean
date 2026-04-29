import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.CircleDimension.RiemannSiegelGabckeLogscaleOrthogonalRecursion

namespace Omega.CircleDimension

/-- Finite-shell package for the logscale energy-equipartition estimate. The inherited fields
record the shell recursion, while the extra fields split each layer energy into a harmonic main
term and an off-diagonal remainder, together with an approximation of the harmonic slice by
`log q`. -/
structure RSLogscaleEnergyEquipartitionData extends RSLogscaleOrthogonalRecursionData where
  q : ℝ
  T : ℝ
  harmonicContribution : ℕ → ℝ
  offDiagonalContribution : ℕ → ℝ
  harmonicError : ℕ → ℝ
  diagonalPlusOffDiagonal :
    ∀ ⦃ℓ : ℕ⦄, ℓ < L →
      layerEnergy ℓ = T * harmonicContribution ℓ + offDiagonalContribution ℓ
  offDiagonalControlled :
    ∀ ⦃ℓ : ℕ⦄, ℓ < L → |offDiagonalContribution ℓ| ≤ shellBound ℓ
  harmonicLogApprox :
    ∀ ⦃ℓ : ℕ⦄, ℓ < L → |harmonicContribution ℓ - Real.log q| ≤ harmonicError ℓ

namespace RSLogscaleEnergyEquipartitionData

/-- The diagonal contribution `T ∑ 1/n` attached to the shell `ℓ`. -/
def harmonicMainTerm (D : RSLogscaleEnergyEquipartitionData) (ℓ : ℕ) : ℝ :=
  D.T * D.harmonicContribution ℓ

/-- The limiting `T log q` main term. -/
noncomputable def asymptoticMainTerm (D : RSLogscaleEnergyEquipartitionData) (_ : ℕ) : ℝ :=
  D.T * Real.log D.q

/-- Each shell energy is controlled both by the diagonal harmonic term and by the asymptotic
`T log q` main term. -/
def layerEnergyEquipartition (D : RSLogscaleEnergyEquipartitionData) : Prop :=
  ∀ ⦃ℓ : ℕ⦄, ℓ < D.L →
    |D.layerEnergy ℓ - D.harmonicMainTerm ℓ| ≤ D.shellBound ℓ ∧
      |D.layerEnergy ℓ - D.asymptoticMainTerm ℓ| ≤
        D.shellBound ℓ + |D.T| * D.harmonicError ℓ

lemma layerEnergyEquipartition_holds (D : RSLogscaleEnergyEquipartitionData) :
    D.layerEnergyEquipartition := by
  intro ℓ hℓ
  have hdecomp := D.diagonalPlusOffDiagonal hℓ
  have hOff := D.offDiagonalControlled hℓ
  have hHarm := D.harmonicLogApprox hℓ
  have hfirst :
      |D.layerEnergy ℓ - D.harmonicMainTerm ℓ| ≤ D.shellBound ℓ := by
    have hrewrite :
        D.layerEnergy ℓ - D.harmonicMainTerm ℓ = D.offDiagonalContribution ℓ := by
      rw [RSLogscaleEnergyEquipartitionData.harmonicMainTerm, hdecomp]
      ring
    rw [hrewrite]
    exact hOff
  refine ⟨hfirst, ?_⟩
  have hsplit :
      D.layerEnergy ℓ - D.asymptoticMainTerm ℓ =
        (D.layerEnergy ℓ - D.harmonicMainTerm ℓ) +
          D.T * (D.harmonicContribution ℓ - Real.log D.q) := by
    unfold asymptoticMainTerm harmonicMainTerm
    ring
  rw [hsplit]
  calc
    |(D.layerEnergy ℓ - D.harmonicMainTerm ℓ) + D.T * (D.harmonicContribution ℓ - Real.log D.q)| ≤
        |D.layerEnergy ℓ - D.harmonicMainTerm ℓ| +
          |D.T * (D.harmonicContribution ℓ - Real.log D.q)| := by
      exact abs_add_le _ _
    _ = |D.layerEnergy ℓ - D.harmonicMainTerm ℓ| +
          |D.T| * |D.harmonicContribution ℓ - Real.log D.q| := by
      rw [abs_mul]
    _ ≤ D.shellBound ℓ + |D.T| * D.harmonicError ℓ := by
      refine add_le_add hfirst ?_
      exact mul_le_mul_of_nonneg_left hHarm (abs_nonneg D.T)

end RSLogscaleEnergyEquipartitionData

open RSLogscaleOrthogonalRecursionData
open RSLogscaleEnergyEquipartitionData

/-- Paper-facing finite-shell statement for the logscale equipartition law. -/
def rsLogscaleEnergyEquipartitionStatement : Prop :=
  ∀ D : RSLogscaleEnergyEquipartitionData,
    D.toRSLogscaleOrthogonalRecursionData.nearOrthogonalDifference ∧
      D.toRSLogscaleOrthogonalRecursionData.energyRecurrence ∧
      D.toRSLogscaleOrthogonalRecursionData.chainTelescoping ∧
      D.layerEnergyEquipartition

/-- Paper label: `cor:cdim-rs-logscale-energy-equipartition`. -/
def paper_cdim_rs_logscale_energy_equipartition : Prop :=
  rsLogscaleEnergyEquipartitionStatement

theorem paper_cdim_rs_logscale_energy_equipartition_verified :
    paper_cdim_rs_logscale_energy_equipartition := by
  unfold paper_cdim_rs_logscale_energy_equipartition rsLogscaleEnergyEquipartitionStatement
  intro D
  have hrec :=
    paper_cdim_rs_logscale_pseudomartingale_orthogonal_recursion
      D.toRSLogscaleOrthogonalRecursionData
  exact ⟨hrec.1, hrec.2.1, hrec.2.2, D.layerEnergyEquipartition_holds⟩

end Omega.CircleDimension
