import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.EA

open scoped BigOperators

noncomputable section

/-- A one-state positive kernel with local constant potential `κ`. -/
noncomputable def equilibriumOneStateKernel (κ θ : ℝ) : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => Real.exp (κ * θ)

/-- The Perron root of the one-state kernel. -/
noncomputable def equilibriumPerronRoot (κ θ : ℝ) : ℝ := Real.exp (κ * θ)

/-- The normalized right Perron vector. -/
noncomputable def equilibriumRightPerronVec : Fin 1 → ℝ := fun _ => 1

/-- The normalized left Perron vector. -/
noncomputable def equilibriumLeftPerronVec : Fin 1 → ℝ := fun _ => 1

/-- The Doob `h`-transform of the one-state kernel. -/
noncomputable def equilibriumTransitionKernel (κ θ : ℝ) (i j : Fin 1) : ℝ :=
  equilibriumOneStateKernel κ θ i j * equilibriumRightPerronVec j /
    (equilibriumPerronRoot κ θ * equilibriumRightPerronVec i)

/-- The local carry observable is constant in the one-state model. -/
noncomputable def equilibriumCarryObservable (κ : ℝ) (_i _j : Fin 1) : ℝ := κ

/-- For the concrete one-state PF model, the left/right eigenvectors are constant, the Doob
transform is a row-stochastic Markov kernel, and the pressure derivative equals the equilibrium
expectation of the local observable.
    prop:kernel-equilibrium-pf -/
theorem paper_kernel_equilibrium_pf (κ θ : ℝ) :
    (∀ i, ∑ j,
      equilibriumOneStateKernel κ θ i j * equilibriumRightPerronVec j =
        equilibriumPerronRoot κ θ * equilibriumRightPerronVec i) ∧
    (∀ j, ∑ i,
      equilibriumLeftPerronVec i * equilibriumOneStateKernel κ θ i j =
        equilibriumPerronRoot κ θ * equilibriumLeftPerronVec j) ∧
    (∑ i, equilibriumLeftPerronVec i * equilibriumRightPerronVec i = 1) ∧
    (∀ i, ∑ j, equilibriumTransitionKernel κ θ i j = 1) ∧
    deriv (fun t => Real.log (equilibriumPerronRoot κ t)) θ =
      ∑ i, ∑ j, equilibriumTransitionKernel κ θ i j * equilibriumCarryObservable κ i j := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    simp [equilibriumOneStateKernel, equilibriumPerronRoot, equilibriumRightPerronVec]
  · intro j
    fin_cases j
    simp [equilibriumOneStateKernel, equilibriumPerronRoot, equilibriumLeftPerronVec]
  · simp [equilibriumLeftPerronVec, equilibriumRightPerronVec]
  · intro i
    fin_cases i
    simp [equilibriumTransitionKernel, equilibriumOneStateKernel, equilibriumPerronRoot,
      equilibriumRightPerronVec]
  · have hFun : (fun t : ℝ => Real.log (equilibriumPerronRoot κ t)) = fun t : ℝ => κ * t := by
      ext t
      simp [equilibriumPerronRoot]
    rw [hFun]
    have hderiv : HasDerivAt (fun t : ℝ => κ * t) κ θ := by
      simpa [mul_comm] using (hasDerivAt_id θ).const_mul κ
    rw [hderiv.deriv]
    simp [equilibriumTransitionKernel, equilibriumCarryObservable, equilibriumOneStateKernel,
      equilibriumPerronRoot, equilibriumRightPerronVec]

end

end Omega.EA
