import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Zeta.XiNullFiberEntropyWindow

namespace Omega.Zeta

open scoped BigOperators
open Omega.POM

noncomputable section

section XiNullStatisticalRadius

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Total variation written on the explicit lifted microstate space. -/
noncomputable def xiNullMicroTV (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : FiberMicrostate d, |μ a - fiberUniformLift d π a|

/-- The observable bias between a lift `μ` and the fiber-uniform lift. -/
noncomputable def xiNullObservableBias (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (f : FiberMicrostate d → ℝ) : ℝ :=
  |(∑ a : FiberMicrostate d, μ a * f a) - ∑ a : FiberMicrostate d, fiberUniformLift d π a * f a|

/-- Concrete data for the statistical-radius corollary at fixed macro marginal `π`. -/
structure XiNullStatisticalRadiusData where
  d : X → ℕ
  hd : ∀ x, 0 < d x
  π : X → ℝ
  μ : FiberMicrostate d → ℝ
  hμ_marginal : ∀ x, fiberMarginal d μ x = π x
  hμ_nonneg : ∀ a, 0 ≤ μ a
  hπ_nonneg : ∀ x, 0 ≤ π x
  hμ_sum : Finset.univ.sum μ = 1
  f : FiberMicrostate d → ℝ
  fSup : ℝ
  hfSup_nonneg : 0 ≤ fSup
  hkl_nonneg : 0 ≤ klDiv μ (fiberUniformLift d π)
  hkl_le_kappa : klDiv μ (fiberUniformLift d π) ≤ xiNullFiberKappa d π
  hPinsker :
    xiNullMicroTV d π μ ≤ Real.sqrt (klDiv μ (fiberUniformLift d π) / 2)
  hObservableTV :
    xiNullObservableBias d π μ f ≤ 2 * fSup * xiNullMicroTV d π μ

/-- The paper-facing statistical-radius package: the KL defect is the explicit entropy gap from
`paper_xi_null_fiber_entropy_window`, hence it is bounded by `κ_m(π)`; Pinsker and the standard
bounded-observable estimate transfer that control to total variation and expectation bias. -/
def XiNullStatisticalRadiusData.statement
    {X : Type*} [Fintype X] [DecidableEq X] (D : XiNullStatisticalRadiusData (X := X)) : Prop :=
  klDiv D.μ (fiberUniformLift D.d D.π) =
      xiNullFiberBaseEntropy D.π + xiNullFiberKappa D.d D.π - liftEntropy D.d D.μ ∧
    0 ≤ klDiv D.μ (fiberUniformLift D.d D.π) ∧
    klDiv D.μ (fiberUniformLift D.d D.π) ≤ xiNullFiberKappa D.d D.π ∧
    xiNullMicroTV D.d D.π D.μ ≤ Real.sqrt (xiNullFiberKappa D.d D.π / 2) ∧
    xiNullObservableBias D.d D.π D.μ D.f ≤
      2 * D.fSup * Real.sqrt (xiNullFiberKappa D.d D.π / 2)

/-- Paper label: `cor:xi-null-statistical-radius`. -/
theorem paper_xi_null_statistical_radius
    {X : Type*} [Fintype X] [DecidableEq X] (D : XiNullStatisticalRadiusData (X := X)) :
    XiNullStatisticalRadiusData.statement D := by
  have hwindow := paper_xi_null_fiber_entropy_window D.d D.hd D.π D.μ D.hμ_marginal D.hμ_nonneg
    D.hπ_nonneg D.hμ_sum
  have hdefect :
      klDiv D.μ (fiberUniformLift D.d D.π) =
        xiNullFiberBaseEntropy D.π + xiNullFiberKappa D.d D.π - liftEntropy D.d D.μ := by
    rcases hwindow with ⟨hledger, -, -, -⟩
    linarith
  have htv_kappa :
      xiNullMicroTV D.d D.π D.μ ≤ Real.sqrt (xiNullFiberKappa D.d D.π / 2) := by
    calc
      xiNullMicroTV D.d D.π D.μ ≤ Real.sqrt (klDiv D.μ (fiberUniformLift D.d D.π) / 2) :=
        D.hPinsker
      _ ≤ Real.sqrt (xiNullFiberKappa D.d D.π / 2) := by
        refine Real.sqrt_le_sqrt ?_
        linarith [D.hkl_nonneg, D.hkl_le_kappa]
  have hobs_kappa :
      xiNullObservableBias D.d D.π D.μ D.f ≤
        2 * D.fSup * Real.sqrt (xiNullFiberKappa D.d D.π / 2) := by
    calc
      xiNullObservableBias D.d D.π D.μ D.f ≤ 2 * D.fSup * xiNullMicroTV D.d D.π D.μ :=
        D.hObservableTV
      _ ≤ 2 * D.fSup * Real.sqrt (xiNullFiberKappa D.d D.π / 2) := by
        have hmul_nonneg : 0 ≤ 2 * D.fSup := by nlinarith [D.hfSup_nonneg]
        exact mul_le_mul_of_nonneg_left htv_kappa hmul_nonneg
  exact ⟨hdefect, D.hkl_nonneg, D.hkl_le_kappa, htv_kappa, hobs_kappa⟩

end XiNullStatisticalRadius

end

end Omega.Zeta
