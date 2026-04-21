import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.CdimArbitraryProfiniteKernel
import Omega.Zeta.XiCarathPickKernelNormalizationRigidity

namespace Omega.Conclusion

open Omega.Zeta

/-- Add a pure imaginary strictification gauge to a Carathéodory interface. -/
def toeplitzGaugeShift (C : ℂ → ℂ) (η : ℝ) : ℂ → ℂ :=
  fun w => C w + Complex.I * (η : ℂ)

/-- A Toeplitz audit is gauge blind when it factors only through the Carath--Pick kernel. -/
def toeplitzAuditFactorsThroughKernel {α : Type*} (audit : (ℂ → ℂ) → α) : Prop :=
  ∀ ⦃F₁ F₂ : ℂ → ℂ⦄,
    (∀ w z : ℂ, carathPickKernel F₁ w z = carathPickKernel F₂ w z) →
      audit F₁ = audit F₂

/-- Adding a pure imaginary constant does not change the Carath--Pick kernel. -/
theorem carathPickKernel_toeplitzGaugeShift (C : ℂ → ℂ) (η : ℝ) :
    ∀ w z : ℂ, carathPickKernel (toeplitzGaugeShift C η) w z = carathPickKernel C w z := by
  intro w z
  simp [carathPickKernel, toeplitzGaugeShift]
  ring

/-- The unit imaginary shift changes the zero interface. -/
theorem toeplitzGaugeShift_zero_ne :
    toeplitzGaugeShift (fun _ : ℂ => 0) 1 ≠ fun _ : ℂ => 0 := by
  intro h
  have h0 := congrFun h 0
  simp [toeplitzGaugeShift] at h0

/-- Paper label: `thm:conclusion-toeplitz-gauge-blindness-zero-dimensional-ledger-necessity`.
Any audit that depends only on Toeplitz/Carath--Pick kernels is blind to strictification gauge
shifts, the existing Carath--Pick rigidity theorem identifies the invisible direction as a unique
imaginary constant, arbitrary profinite kernels occur at fixed visible circle dimension, and such
an audit therefore cannot recover the strictification gauge. -/
theorem paper_conclusion_toeplitz_gauge_blindness_zero_dimensional_ledger_necessity
    {α : Type*} (audit : (ℂ → ℂ) → α) (hAudit : toeplitzAuditFactorsThroughKernel audit)
    (r : ℕ) (D : ProfiniteKernelRealizationData) :
    (∀ C η, audit (toeplitzGaugeShift C η) = audit C) ∧
      (∀ C η, ∃! β : ℝ, ∀ w : ℂ, toeplitzGaugeShift C η w = C w + Complex.I * (β : ℂ)) ∧
      (∃ G : Type, D.circleDim G = r ∧ Nonempty (D.pontryaginDual G ≃ D.circleFactor r × D.kernel)) ∧
      ¬ Function.Injective audit := by
  refine ⟨?_, ?_, paper_conclusion_cdim_arbitrary_profinite_kernel r D, ?_⟩
  · intro C η
    exact hAudit (carathPickKernel_toeplitzGaugeShift C η)
  · intro C η
    exact paper_xi_carath_pick_kernel_normalization_rigidity
      (toeplitzGaugeShift C η) C (carathPickKernel_toeplitzGaugeShift C η)
  · intro hInjective
    have hBlind :
        audit (toeplitzGaugeShift (fun _ : ℂ => 0) 1) = audit (fun _ : ℂ => 0) :=
      hAudit (carathPickKernel_toeplitzGaugeShift (fun _ : ℂ => 0) 1)
    have hEq :
        toeplitzGaugeShift (fun _ : ℂ => 0) 1 = fun _ : ℂ => 0 :=
      hInjective hBlind
    exact toeplitzGaugeShift_zero_ne hEq

end Omega.Conclusion
