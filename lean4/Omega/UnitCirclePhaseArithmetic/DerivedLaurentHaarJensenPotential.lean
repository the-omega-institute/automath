import Omega.UnitCirclePhaseArithmetic.AppJensenDefectLogDerivative
import Omega.UnitCirclePhaseArithmetic.AppJensenDefectPowerCovariance
import Omega.UnitCirclePhaseArithmetic.DerivedTwoTermLaurentSingularRing
import Omega.UnitCirclePhaseArithmetic.LeyangHaarPushforwardDensity

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Paper label: `thm:derived-laurent-haar-jensen-potential`. -/
def derived_laurent_haar_jensen_potential_statement : Prop :=
  (∀ (A B w : ℂ) (M N : ℕ), w ≠ 0 → A ≠ 0 → B ≠ 0 → 1 ≤ N → N < M →
    (twoTermLaurentDerivative A B M N w = 0 ↔
      w ^ (M - N) = twoTermLaurentCriticalRatio A B M N ∧
        ‖w‖ ^ (M - N) = ‖twoTermLaurentCriticalRatio A B M N‖)) ∧
  (∀ t : ℝ,
    leyangHaarPushforwardDensity t =
      if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0) ∧
  (∀ (roots : Finset ℂ), (∀ z ∈ roots, 0 < ‖z‖) →
    Continuous (fun s => appSingleZeroJensenDefect (Real.exp s) roots) ∧
      Monotone (fun s => appSingleZeroJensenDefect (Real.exp s) roots)) ∧
  (∀ (m : ℕ), 1 ≤ m → (energyF energyG entropyF entropyG : ℝ) →
    energyG = energyF → entropyG = entropyF →
      appJensenDefect energyG entropyG = appJensenDefect energyF entropyF)

theorem paper_derived_laurent_haar_jensen_potential :
    derived_laurent_haar_jensen_potential_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun A B w M N hw hA hB hN hMN =>
      paper_derived_two_term_laurent_singular_ring A B w M N hw hA hB hN hMN
  · intro t
    exact (paper_leyang_haar_pushforward_density.2.1) t
  · intro roots hroot_pos
    exact ⟨(paper_app_jensen_defect_log_derivative roots hroot_pos).2.1,
      (paper_app_jensen_defect_log_derivative roots hroot_pos).2.2.1⟩
  · intro m hm energyF energyG entropyF entropyG hEnergy hEntropy
    exact paper_app_jensen_defect_power_covariance m hm energyF energyG entropyF entropyG
      hEnergy hEntropy

end

end Omega.UnitCirclePhaseArithmetic
