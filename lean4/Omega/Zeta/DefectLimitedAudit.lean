import Mathlib.Tactic
import Omega.Zeta.XiNullStatisticalRadius

namespace Omega.Zeta

open scoped BigOperators
open Omega.POM

noncomputable section

section

variable {X : Type*} [Fintype X] [DecidableEq X]

private lemma observableBias_le_two_mul_tv
    (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) (f : FiberMicrostate d → ℝ)
    (fSup : ℝ) (hfSup : ∀ a, |f a| ≤ fSup) :
    xiNullObservableBias d π μ f ≤ 2 * fSup * xiNullMicroTV d π μ := by
  unfold xiNullObservableBias xiNullMicroTV
  calc
    |(∑ a : FiberMicrostate d, μ a * f a) - ∑ a : FiberMicrostate d, fiberUniformLift d π a * f a|
        = |∑ a : FiberMicrostate d, (μ a - fiberUniformLift d π a) * f a| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro a ha
            ring
    _ ≤ ∑ a : FiberMicrostate d, |(μ a - fiberUniformLift d π a) * f a| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : FiberMicrostate d, |μ a - fiberUniformLift d π a| * |f a| := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [abs_mul]
    _ ≤ ∑ a : FiberMicrostate d, |μ a - fiberUniformLift d π a| * fSup := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact mul_le_mul_of_nonneg_left (hfSup a) (abs_nonneg _)
    _ = fSup * ∑ a : FiberMicrostate d, |μ a - fiberUniformLift d π a| := by
          symm
          calc
            fSup * ∑ a : FiberMicrostate d, |μ a - fiberUniformLift d π a|
                = ∑ a : FiberMicrostate d, fSup * |μ a - fiberUniformLift d π a| := by
                    simpa using
                      (Finset.mul_sum (s := Finset.univ)
                        (f := fun a : FiberMicrostate d => |μ a - fiberUniformLift d π a|) fSup)
            _ = ∑ a : FiberMicrostate d, |μ a - fiberUniformLift d π a| * fSup := by
                    refine Finset.sum_congr rfl ?_
                    intro a ha
                    ring
    _ = 2 * fSup * ((1 / 2 : ℝ) * ∑ a : FiberMicrostate d, |μ a - fiberUniformLift d π a|) := by
          ring
    _ = 2 * fSup * xiNullMicroTV d π μ := by rfl

/-- Paper label: `thm:defect-limited-audit`.
Given the fiberwise KL audit bound `D_KL(μ || π̃) ≤ κ_m(π)`, Pinsker upgrades it to the
total-variation radius, and the standard bounded-observable estimate transfers the same scale to
expectation bias. -/
theorem paper_defect_limited_audit
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) (hμ_nonneg : ∀ a, 0 ≤ μ a)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hμ_sum : Finset.univ.sum μ = 1)
    (f : FiberMicrostate d → ℝ) (fSup : ℝ) (hfSup_nonneg : 0 ≤ fSup)
    (hfSup : ∀ a, |f a| ≤ fSup)
    (hkl_nonneg : 0 ≤ klDiv μ (fiberUniformLift d π))
    (hkl_le_kappa : klDiv μ (fiberUniformLift d π) ≤ xiNullFiberKappa d π)
    (hPinsker : xiNullMicroTV d π μ ≤ Real.sqrt (klDiv μ (fiberUniformLift d π) / 2)) :
    klDiv μ (fiberUniformLift d π) ≤ xiNullFiberKappa d π ∧
      xiNullMicroTV d π μ ≤ Real.sqrt (xiNullFiberKappa d π / 2) ∧
      xiNullObservableBias d π μ f ≤ 2 * fSup * Real.sqrt (xiNullFiberKappa d π / 2) := by
  let D : XiNullStatisticalRadiusData (X := X) :=
    { d := d
      hd := hd
      π := π
      μ := μ
      hμ_marginal := hμ_marginal
      hμ_nonneg := hμ_nonneg
      hπ_nonneg := hπ_nonneg
      hμ_sum := hμ_sum
      f := f
      fSup := fSup
      hfSup_nonneg := hfSup_nonneg
      hkl_nonneg := hkl_nonneg
      hkl_le_kappa := hkl_le_kappa
      hPinsker := hPinsker
      hObservableTV := observableBias_le_two_mul_tv d π μ f fSup hfSup }
  have hstat := paper_xi_null_statistical_radius D
  exact ⟨hstat.2.2.1, hstat.2.2.2.1, hstat.2.2.2.2⟩

end

end

end Omega.Zeta
