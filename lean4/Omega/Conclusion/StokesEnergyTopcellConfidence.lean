import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.StokesEnergyCellSamplingConcentration
import Omega.Conclusion.StokesEnergyH1SecondOrder

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-stokes-energy-topcell-confidence`. The cell-sampling
concentration estimate controls the fluctuation around the discrete energy, a triangle-inequality
step compares the discrete energy with the target `L²` energy, and the existing second-order
`H¹` estimate gives the strengthened deterministic bias bound. -/
theorem paper_conclusion_stokes_energy_topcell_confidence
    {n : ℕ} (hn : 0 < n) (M discreteEnergy totalEnergy radius : ℝ) (X : Fin n → ℝ)
    (hX : ∀ j, 0 ≤ X j ∧ X j ≤ M ^ 2)
    (hHoeffding : stokesHoeffdingEvent X discreteEnergy radius)
    (hdiscrete_le : discreteEnergy ≤ totalEnergy)
    (D : StokesEnergyH1SecondOrderData)
    (hbias : totalEnergy - discreteEnergy = D.globalSecondOrderError) :
    |stokesCellEmpiricalMean X - totalEnergy| ≤ (totalEnergy - discreteEnergy) + radius ∧
      totalEnergy - discreteEnergy ≤ D.totalH1 * dyadicSecondOrderRate D.m := by
  have hconc :=
    paper_conclusion_stokes_energy_cell_sampling_concentration
      (hn := hn) (M := M) (hPow := 1) (cellVolume := 1) (expectation := discreteEnergy)
      (radius := radius) (X := X) hX hHoeffding
  have hdev : |stokesCellEmpiricalMean X - discreteEnergy| ≤ radius := by
    simpa [stokesRescaledDeviation] using hconc.2
  have hbias_nonneg : 0 ≤ totalEnergy - discreteEnergy := sub_nonneg.mpr hdiscrete_le
  have htriangle :
      |stokesCellEmpiricalMean X - totalEnergy| ≤
        |stokesCellEmpiricalMean X - discreteEnergy| + |discreteEnergy - totalEnergy| := by
    have := abs_sub_le (stokesCellEmpiricalMean X) discreteEnergy totalEnergy
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hbias_abs : |discreteEnergy - totalEnergy| = totalEnergy - discreteEnergy := by
    calc
      |discreteEnergy - totalEnergy| = -(discreteEnergy - totalEnergy) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hdiscrete_le)]
      _ = totalEnergy - discreteEnergy := by ring
  have hsecond :
      totalEnergy - discreteEnergy ≤ D.totalH1 * dyadicSecondOrderRate D.m := by
    rw [hbias]
    exact paper_conclusion_stokes_energy_h1_second_order D
  constructor
  · calc
      |stokesCellEmpiricalMean X - totalEnergy|
          ≤ |stokesCellEmpiricalMean X - discreteEnergy| + |discreteEnergy - totalEnergy| :=
            htriangle
      _ = |stokesCellEmpiricalMean X - discreteEnergy| + (totalEnergy - discreteEnergy) := by
            rw [hbias_abs]
      _ ≤ radius + (totalEnergy - discreteEnergy) := by
            gcongr
      _ = (totalEnergy - discreteEnergy) + radius := by ring
  · exact hsecond

end Omega.Conclusion
