import Mathlib.Tactic
import Omega.Folding.MicrostateResidualWindowReachability
import Omega.POM.IprojGapExact
import Omega.POM.IprojMaxent

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Paper label: `cor:pom-micro-slip-window`. The microstate KL distance to the global uniform
baseline lies in an explicit interval whose width is the residual window determined by the macro
marginal and the fiber sizes. -/
theorem paper_pom_micro_slip_window {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) (uΩ : FiberMicrostate d → ℝ)
    (w : X → ℝ) (hμ_marginal : ∀ x, fiberMarginal d μ x = π x)
    (hUniformMicro : ∀ a, uΩ a = (1 : ℝ) / Fintype.card (FiberMicrostate d))
    (hUniformPush : ∀ x, w x = (d x : ℝ) / Fintype.card (FiberMicrostate d))
    (hμ_nonneg : ∀ a, 0 ≤ μ a) (hπ_nonneg : ∀ x, 0 ≤ π x) (hμ_sum : Finset.univ.sum μ = 1) :
    klDiv (fiberUniformLift d π) uΩ ≤ klDiv μ uΩ ∧
      klDiv μ uΩ ≤ klDiv (fiberUniformLift d π) uΩ + Omega.Folding.residualWindow π d := by
  have hgap :
      klDiv μ uΩ - klDiv (fiberUniformLift d π) uΩ = klDiv μ (fiberUniformLift d π) :=
    paper_pom_iproj_gap_exact d hd π μ uΩ w hμ_marginal hUniformMicro hUniformPush hμ_nonneg
      hπ_nonneg hμ_sum
  have hdefect :
      klDiv μ (fiberUniformLift d π) =
        liftEntropy d (fiberUniformLift d π) - liftEntropy d μ :=
    paper_pom_kl_defect_identity d hd π μ hμ_marginal hμ_nonneg hπ_nonneg hμ_sum
  have hmaxent :
      liftEntropy d μ ≤ liftEntropy d (fiberUniformLift d π) :=
    paper_pom_iproj_maxent d hd π μ hμ_marginal hμ_nonneg hπ_nonneg hμ_sum
  have hkl_nonneg : 0 ≤ klDiv μ (fiberUniformLift d π) := by
    rw [hdefect]
    linarith
  have hlower : klDiv (fiberUniformLift d π) uΩ ≤ klDiv μ uΩ := by
    linarith
  have hcond_entropy_nonneg : ∀ x, 0 ≤ fiberConditionalEntropy d π μ x := by
    intro x
    unfold fiberConditionalEntropy
    refine Finset.sum_nonneg ?_
    intro i hi
    by_cases hπ0 : π x = 0
    · simp [fiberConditionalLaw, hπ0]
    · have hπ_pos : 0 < π x := lt_of_le_of_ne (hπ_nonneg x) (Ne.symm hπ0)
      have hterm_nonneg : 0 ≤ fiberConditionalLaw d π μ x i := by
        simp [fiberConditionalLaw, hπ0, div_nonneg, hμ_nonneg ⟨x, i⟩, le_of_lt hπ_pos]
      have hμ_le_pi : μ ⟨x, i⟩ ≤ π x := by
        calc
          μ ⟨x, i⟩ ≤ fiberMarginal d μ x := by
            simpa [fiberMarginal] using
              (Finset.single_le_sum (fun j _ => hμ_nonneg ⟨x, j⟩) (Finset.mem_univ i))
          _ = π x := hμ_marginal x
      have hterm_le_one : fiberConditionalLaw d π μ x i ≤ 1 := by
        simp [fiberConditionalLaw, hπ0]
        exact (div_le_iff₀ hπ_pos).2 (by simpa using hμ_le_pi)
      exact Real.negMulLog_nonneg hterm_nonneg hterm_le_one
  have hdefect_window :
      klDiv μ (fiberUniformLift d π) ≤ Omega.Folding.residualWindow π d := by
    rw [paper_pom_fiber_entropy_deficit d hd π μ hμ_marginal hμ_nonneg,
      Omega.Folding.residualWindow]
    refine Finset.sum_le_sum ?_
    intro x hx
    have hsub :
        Real.log (d x) - fiberConditionalEntropy d π μ x ≤ Real.log (d x) := by
      linarith [hcond_entropy_nonneg x]
    exact mul_le_mul_of_nonneg_left hsub (hπ_nonneg x)
  have hupper : klDiv μ uΩ ≤ klDiv (fiberUniformLift d π) uΩ + Omega.Folding.residualWindow π d :=
    by
      linarith
  exact ⟨hlower, hupper⟩

end

end Omega.POM
