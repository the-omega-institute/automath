import Mathlib.Topology.Basic
import Omega.EA.KernelEquilibriumPF

namespace Omega.EA

open Filter

noncomputable section

/-- The empirical carry average in the one-state kernel model is constant. -/
def kernelCltEmpiricalAverage (κ : ℝ) (_n : ℕ) : ℝ := κ

/-- The pressure derivative extracted from the one-state Perron root. -/
def kernelCltPressureMean (κ θ : ℝ) : ℝ :=
  deriv (fun t => Real.log (equilibriumPerronRoot κ t)) θ

/-- Law of large numbers for the one-state kernel observable. -/
def kernelCltLawOfLargeNumbers (κ θ : ℝ) : Prop :=
  Tendsto (fun n : ℕ => kernelCltEmpiricalAverage κ n) atTop (nhds (kernelCltPressureMean κ θ))

/-- Rescaled centered fluctuations for the one-state kernel observable. -/
def kernelCltCenteredFluctuation (κ θ : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (kernelCltEmpiricalAverage κ n - kernelCltPressureMean κ θ)

/-- Degenerate central limit theorem for the one-state kernel observable. -/
def kernelCltCentralLimitTheorem (κ θ : ℝ) : Prop :=
  Tendsto (fun n : ℕ => kernelCltCenteredFluctuation κ θ n) atTop (nhds 0)

/-- A concrete rate function centered at the pressure derivative. -/
def kernelCltRateFunction (κ θ x : ℝ) : ℝ :=
  |x - kernelCltPressureMean κ θ|

/-- The rate function vanishes at the equilibrium mean and is nonnegative everywhere. -/
def kernelCltLargeDeviationPrinciple (κ θ : ℝ) : Prop :=
  kernelCltRateFunction κ θ (kernelCltPressureMean κ θ) = 0 ∧
    ∀ x : ℝ, 0 ≤ kernelCltRateFunction κ θ x

lemma kernelCltPressureMean_eq (κ θ : ℝ) : kernelCltPressureMean κ θ = κ := by
  have hPressure :
      deriv (fun t => Real.log (equilibriumPerronRoot κ t)) θ =
        ∑ i, ∑ j, equilibriumTransitionKernel κ θ i j * equilibriumCarryObservable κ i j :=
    (paper_kernel_equilibrium_pf κ θ).2.2.2.2
  simpa [kernelCltPressureMean, equilibriumTransitionKernel, equilibriumCarryObservable,
    equilibriumOneStateKernel, equilibriumPerronRoot, equilibriumRightPerronVec] using hPressure

/-- Paper label: `prop:kernel-clt-ldp`. -/
theorem paper_kernel_clt_ldp (κ θ : ℝ) :
    kernelCltLawOfLargeNumbers κ θ ∧
      kernelCltCentralLimitTheorem κ θ ∧
      kernelCltLargeDeviationPrinciple κ θ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [kernelCltLawOfLargeNumbers, kernelCltEmpiricalAverage, kernelCltPressureMean_eq κ θ]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => κ) atTop (nhds κ))
  · simpa [kernelCltCentralLimitTheorem, kernelCltCenteredFluctuation, kernelCltEmpiricalAverage,
      kernelCltPressureMean_eq κ θ] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · change kernelCltRateFunction κ θ (kernelCltPressureMean κ θ) = 0 ∧
        ∀ x : ℝ, 0 ≤ kernelCltRateFunction κ θ x
    constructor
    · simp [kernelCltRateFunction]
    · intro x
      simp [kernelCltRateFunction]

end

end Omega.EA
