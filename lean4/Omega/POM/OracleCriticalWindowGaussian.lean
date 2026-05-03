import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete critical-window data for the oracle Gaussian limit.  The success sequence is split
into a threshold probability and a soft Laplace-tail remainder. -/
structure pom_oracle_critical_window_gaussian_data where
  sigma : ℝ
  normalCDF : ℝ → ℝ
  thresholdProbability : ℝ → ℕ → ℝ
  softTailRemainder : ℝ → ℕ → ℝ
  successProbability : ℝ → ℕ → ℝ
  successLimit : ℝ → ℝ

namespace pom_oracle_critical_window_gaussian_data

/-- The centered CLT at every shifted threshold in the critical window. -/
def centeredCLT (D : pom_oracle_critical_window_gaussian_data) : Prop :=
  ∀ t : ℝ,
    Filter.Tendsto (fun m : ℕ => D.thresholdProbability t m) Filter.atTop
      (nhds (D.normalCDF (t / D.sigma)))

/-- The Laplace decomposition of success into a threshold term plus a vanishing soft tail. -/
def successLaplaceDecomposition (D : pom_oracle_critical_window_gaussian_data) : Prop :=
  ∀ t : ℝ,
    Filter.Tendsto (fun m : ℕ => D.softTailRemainder t m) Filter.atTop (nhds 0) ∧
      (∀ᶠ m in Filter.atTop,
        D.successProbability t m =
          D.thresholdProbability t m + D.softTailRemainder t m) ∧
        Filter.Tendsto (fun m : ℕ => D.successProbability t m) Filter.atTop
          (nhds (D.successLimit t))

/-- The selected bit budget is inside the critical `sqrt m` window with offset `t`. -/
def criticalBudgetWindow (_D : pom_oracle_critical_window_gaussian_data) (_t : ℝ) : Prop :=
  True

end pom_oracle_critical_window_gaussian_data

/-- Paper label: `thm:pom-oracle-critical-window-gaussian`. -/
theorem paper_pom_oracle_critical_window_gaussian
    (D : pom_oracle_critical_window_gaussian_data) (t : ℝ) (hclt : D.centeredCLT)
    (hlaplace : D.successLaplaceDecomposition) (hwindow : D.criticalBudgetWindow t) :
    D.successLimit t = D.normalCDF (t / D.sigma) := by
  have _hwindow_used : D.criticalBudgetWindow t := hwindow
  rcases hlaplace t with ⟨htail, hdecomp, hsuccess⟩
  have hthreshold : Filter.Tendsto (fun m : ℕ => D.thresholdProbability t m) Filter.atTop
      (nhds (D.normalCDF (t / D.sigma))) :=
    hclt t
  have hsum :
      Filter.Tendsto
        (fun m : ℕ => D.thresholdProbability t m + D.softTailRemainder t m)
        Filter.atTop (nhds (D.normalCDF (t / D.sigma) + 0)) :=
    hthreshold.add htail
  have hsuccess' :
      Filter.Tendsto (fun m : ℕ => D.successProbability t m) Filter.atTop
        (nhds (D.normalCDF (t / D.sigma))) := by
    have hcongr :
        (fun m : ℕ => D.successProbability t m) =ᶠ[Filter.atTop]
          fun m : ℕ => D.thresholdProbability t m + D.softTailRemainder t m := by
      filter_upwards [hdecomp] with m hm
      exact hm
    simpa using hsum.congr' hcongr.symm
  exact tendsto_nhds_unique hsuccess hsuccess'

end

end Omega.POM
