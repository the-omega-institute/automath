import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import Omega.POM.KLDefectIdentity

namespace Omega.Conclusion

open scoped BigOperators
open Omega.POM

section

variable {X : Type*} [Fintype X] [DecidableEq X]

private lemma microstate_eq_zero_of_zero_marginal
    (d : X → ℕ) (μ : FiberMicrostate d → ℝ) (hμ_nonneg : ∀ a, 0 ≤ μ a)
    {x : X} (hx : fiberMarginal d μ x = 0) (i : Fin (d x)) :
    μ ⟨x, i⟩ = 0 := by
  have hle : μ ⟨x, i⟩ ≤ fiberMarginal d μ x := by
    simpa [fiberMarginal] using
      (Finset.single_le_sum (fun j _ => hμ_nonneg ⟨x, j⟩) (Finset.mem_univ i))
  have hnonneg : 0 ≤ μ ⟨x, i⟩ := hμ_nonneg ⟨x, i⟩
  rw [hx] at hle
  linarith

private lemma fold_audit_kl_pythagoras
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π ν : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x)
    (hμ_nonneg : ∀ a, 0 ≤ μ a) (hν_pos : ∀ x, 0 < ν x) :
    klDiv μ (fiberUniformLift d ν) = klDiv π ν + klDiv μ (fiberUniformLift d π) := by
  have hsplit :
      klDiv μ (fiberUniformLift d ν) =
        klDiv μ (fiberUniformLift d π) + ∑ a, μ a * Real.log (π a.1 / ν a.1) := by
    unfold klDiv
    calc
      ∑ a, μ a * Real.log (μ a / fiberUniformLift d ν a)
          = ∑ a, (μ a * Real.log (μ a / fiberUniformLift d π a) +
              μ a * Real.log (π a.1 / ν a.1)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rcases a with ⟨x, i⟩
              by_cases hπ0 : π x = 0
              · have hμ0 : μ ⟨x, i⟩ = 0 := by
                  have hx0 : fiberMarginal d μ x = 0 := by rw [hμ_marginal x, hπ0]
                  exact microstate_eq_zero_of_zero_marginal d μ hμ_nonneg hx0 i
                simp [fiberUniformLift, hπ0, hμ0]
              · have hd0 : (d x : ℝ) ≠ 0 := by
                  exact_mod_cast Nat.ne_of_gt (hd x)
                have hν0 : ν x ≠ 0 := ne_of_gt (hν_pos x)
                by_cases hμ0 : μ ⟨x, i⟩ = 0
                · simp [hμ0]
                · have hfactor :
                    μ ⟨x, i⟩ / fiberUniformLift d ν ⟨x, i⟩ =
                      (μ ⟨x, i⟩ / fiberUniformLift d π ⟨x, i⟩) * (π x / ν x) := by
                    unfold fiberUniformLift
                    field_simp [hd0, hπ0, hν0]
                  rw [hfactor]
                  rw [Real.log_mul]
                  · ring
                  · exact div_ne_zero hμ0 (by simp [fiberUniformLift, hπ0, hd0])
                  · exact div_ne_zero hπ0 hν0
      _ = (∑ a, μ a * Real.log (μ a / fiberUniformLift d π a)) +
            ∑ a, μ a * Real.log (π a.1 / ν a.1) := by
              rw [Finset.sum_add_distrib]
      _ = klDiv μ (fiberUniformLift d π) + ∑ a, μ a * Real.log (π a.1 / ν a.1) := by
              simp [klDiv]
  have hfiber :
      (∑ a, μ a * Real.log (π a.1 / ν a.1)) = klDiv π ν := by
    rw [Fintype.sum_sigma, klDiv]
    refine Eq.trans ?_ rfl
    refine Finset.sum_congr rfl ?_
    intro x hx
    calc
      ∑ i : Fin (d x), μ ⟨x, i⟩ * Real.log (π x / ν x)
          = (∑ i : Fin (d x), μ ⟨x, i⟩) * Real.log (π x / ν x) := by
              rw [← Finset.sum_mul]
      _ = fiberMarginal d μ x * Real.log (π x / ν x) := by simp [fiberMarginal]
      _ = π x * Real.log (π x / ν x) := by rw [hμ_marginal x]
  calc
    klDiv μ (fiberUniformLift d ν)
        = klDiv μ (fiberUniformLift d π) + ∑ a, μ a * Real.log (π a.1 / ν a.1) := hsplit
    _ = klDiv π ν + klDiv μ (fiberUniformLift d π) := by rw [hfiber]; ring

/-- The grouped fiberwise expansion of the audit KL defect. -/
def foldAuditFiberwiseExpansion (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) : Prop :=
  klDiv μ (fiberUniformLift d π) =
    ∑ x : X, ∑ i : Fin (d x), μ ⟨x, i⟩ * Real.log (μ ⟨x, i⟩ / (π x / d x))

/-- The finite-fiber fold audit satisfies the exact KL-Pythagoras identity, the entropy-gap
identity, and the corresponding fiberwise expansion.
    thm:conclusion-fold-audit-kl-pythagoras -/
theorem paper_conclusion_fold_audit_kl_pythagoras
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π ν : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) (hμ_nonneg : ∀ a, 0 ≤ μ a)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hν_pos : ∀ x, 0 < ν x) (hμ_sum : Finset.univ.sum μ = 1) :
    klDiv μ (fiberUniformLift d ν) = klDiv π ν + klDiv μ (fiberUniformLift d π) ∧
      klDiv μ (fiberUniformLift d π) =
        liftEntropy d (fiberUniformLift d π) - liftEntropy d μ ∧
      foldAuditFiberwiseExpansion d π μ := by
  refine ⟨fold_audit_kl_pythagoras d hd π ν μ hμ_marginal hμ_nonneg hν_pos, ?_, ?_⟩
  · exact paper_pom_kl_defect_identity d hd π μ hμ_marginal hμ_nonneg hπ_nonneg hμ_sum
  · unfold foldAuditFiberwiseExpansion klDiv
    rw [Fintype.sum_sigma]
    simp [fiberUniformLift]

end

end Omega.Conclusion
