import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import Omega.POM.KLDefectIdentity

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

private lemma fiberUniformLift_marginal
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) :
    ∀ x, fiberMarginal d (fiberUniformLift d π) x = π x := by
  intro x
  have hd0 : (d x : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (hd x)
  calc
    fiberMarginal d (fiberUniformLift d π) x = ∑ _i : Fin (d x), π x / d x := by
      simp [fiberMarginal, fiberUniformLift]
    _ = (d x : ℝ) * (π x / d x) := by simp
    _ = π x := by
      field_simp [hd0]

private lemma pi_sum_eq_one
    (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) (hμ_sum : Finset.univ.sum μ = 1) :
    Finset.univ.sum π = 1 := by
  calc
    Finset.univ.sum π = ∑ x : X, fiberMarginal d μ x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [hμ_marginal x]
    _ = Finset.univ.sum μ := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp [fiberMarginal]
    _ = 1 := hμ_sum

private lemma fiberMicrostate_card_pos
    (d : X → ℕ) (μ : FiberMicrostate d → ℝ) (hμ_sum : Finset.univ.sum μ = 1) :
    0 < Fintype.card (FiberMicrostate d) := by
  by_contra hcard
  have hEmpty : IsEmpty (FiberMicrostate d) :=
    Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hcard)
  letI := hEmpty
  have hsum0 : Finset.univ.sum μ = 0 := by
    simp
  rw [hsum0] at hμ_sum
  norm_num at hμ_sum

private lemma klDiv_uniform_micro_eq_log_card_sub_entropy
    (d : X → ℕ) (μ : FiberMicrostate d → ℝ) (uΩ : FiberMicrostate d → ℝ)
    (hUniformMicro : ∀ a, uΩ a = (1 : ℝ) / Fintype.card (FiberMicrostate d))
    (hμ_sum : Finset.univ.sum μ = 1) :
    klDiv μ uΩ = Real.log (Fintype.card (FiberMicrostate d)) - liftEntropy d μ := by
  let Ω := Fintype.card (FiberMicrostate d)
  have hΩpos : 0 < Ω := fiberMicrostate_card_pos d μ hμ_sum
  have hΩ0 : (Ω : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hΩpos
  have hsplit :
      klDiv μ uΩ =
        (∑ a, -Real.negMulLog (μ a)) + ∑ a, μ a * Real.log Ω := by
    unfold klDiv
    calc
      ∑ a, μ a * Real.log (μ a / uΩ a)
          = ∑ a, (-Real.negMulLog (μ a) + μ a * Real.log Ω) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [hUniformMicro a]
              by_cases hμ0 : μ a = 0
              · simp [hμ0]
              · have hdiv : μ a / ((1 : ℝ) / Ω) = μ a * Ω := by
                  field_simp [hΩ0]
                rw [hdiv, Real.log_mul hμ0 hΩ0, Real.negMulLog]
                ring
      _ = (∑ a, -Real.negMulLog (μ a)) + ∑ a, μ a * Real.log Ω := by
            rw [Finset.sum_add_distrib]
  have hnegEntropy : (∑ a, -Real.negMulLog (μ a)) = -liftEntropy d μ := by
    simp [liftEntropy, fiberEntropy, Fintype.sum_sigma]
  calc
    klDiv μ uΩ = (∑ a, -Real.negMulLog (μ a)) + ∑ a, μ a * Real.log Ω := hsplit
    _ = -liftEntropy d μ + ∑ a, μ a * Real.log Ω := by rw [hnegEntropy]
    _ = -liftEntropy d μ + (∑ a, μ a) * Real.log Ω := by rw [← Finset.sum_mul]
    _ = Real.log Ω - liftEntropy d μ := by rw [hμ_sum]; ring

private lemma klDiv_uniform_macro_eq_log_card_sub_liftEntropy
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) (w : X → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x)
    (hUniformPush : ∀ x, w x = (d x : ℝ) / Fintype.card (FiberMicrostate d))
    (hμ_sum : Finset.univ.sum μ = 1) :
    klDiv π w = Real.log (Fintype.card (FiberMicrostate d)) - liftEntropy d (fiberUniformLift d π) := by
  let Ω := Fintype.card (FiberMicrostate d)
  have hΩpos : 0 < Ω := fiberMicrostate_card_pos d μ hμ_sum
  have hΩ0 : (Ω : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hΩpos
  have hπ_sum : Finset.univ.sum π = 1 := pi_sum_eq_one d π μ hμ_marginal hμ_sum
  have hLiftEntropy :
      liftEntropy d (fiberUniformLift d π) =
        (∑ x : X, Real.negMulLog (π x)) + ∑ x : X, π x * Real.log (d x) := by
    exact
      (paper_pom_maxent_lift d hd π (fiberUniformLift d π)
        (by intro x i j; rfl) (fiberUniformLift_marginal d hd π)).2
  have hsplit :
      klDiv π w =
        (∑ x : X, -Real.negMulLog (π x)) +
          ∑ x : X, π x * (Real.log Ω - Real.log (d x)) := by
    unfold klDiv
    calc
      ∑ x : X, π x * Real.log (π x / w x)
          = ∑ x : X,
              (-Real.negMulLog (π x) + π x * (Real.log Ω - Real.log (d x))) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [hUniformPush x]
              by_cases hπ0 : π x = 0
              · simp [hπ0]
              · have hd0 : (d x : ℝ) ≠ 0 := by
                  exact_mod_cast Nat.ne_of_gt (hd x)
                have hw0 : (d x : ℝ) / Ω ≠ 0 := by
                  exact div_ne_zero hd0 hΩ0
                rw [Real.log_div hπ0 hw0, Real.negMulLog]
                rw [Real.log_div hd0 hΩ0]
                ring
      _ = (∑ x : X, -Real.negMulLog (π x)) +
            ∑ x : X, π x * (Real.log Ω - Real.log (d x)) := by
              rw [Finset.sum_add_distrib]
  calc
    klDiv π w = (∑ x : X, -Real.negMulLog (π x)) + ∑ x : X, π x * (Real.log Ω - Real.log (d x)) :=
      hsplit
    _ = (∑ x : X, -Real.negMulLog (π x)) +
          ((∑ x : X, π x * Real.log Ω) - ∑ x : X, π x * Real.log (d x)) := by
            congr 1
            calc
              ∑ x : X, π x * (Real.log Ω - Real.log (d x)) =
                  ∑ x : X, (π x * Real.log Ω - π x * Real.log (d x)) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    ring
              _ = (∑ x : X, π x * Real.log Ω) - ∑ x : X, π x * Real.log (d x) := by
                    rw [Finset.sum_sub_distrib]
    _ = (∑ x : X, -Real.negMulLog (π x)) +
          ((∑ x : X, π x) * Real.log Ω - ∑ x : X, π x * Real.log (d x)) := by
            rw [← Finset.sum_mul]
    _ = Real.log Ω - ((∑ x : X, Real.negMulLog (π x)) + ∑ x : X, π x * Real.log (d x)) := by
            rw [hπ_sum]
            have hNeg :
                (∑ x : X, -Real.negMulLog (π x)) = -(∑ x : X, Real.negMulLog (π x)) := by
              simpa using
                (Finset.sum_neg_distrib
                  (s := (Finset.univ : Finset X))
                  (f := fun x : X => Real.negMulLog (π x)))
            rw [hNeg]
            ring
    _ = Real.log Ω - liftEntropy d (fiberUniformLift d π) := by
            rw [hLiftEntropy]

/-- Exact KL Pythagoras decomposition from a microstate law to the global uniform baseline.
    thm:pom-kl-pythagoras-uniform -/
theorem paper_pom_kl_pythagoras_uniform {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) (uΩ : FiberMicrostate d → ℝ)
    (w : X → ℝ) (hμ_marginal : ∀ x, fiberMarginal d μ x = π x)
    (hUniformMicro : ∀ a, uΩ a = (1 : ℝ) / Fintype.card (FiberMicrostate d))
    (hUniformPush : ∀ x, w x = (d x : ℝ) / Fintype.card (FiberMicrostate d))
    (hμ_nonneg : ∀ a, 0 ≤ μ a) (hπ_nonneg : ∀ x, 0 ≤ π x) (hμ_sum : Finset.univ.sum μ = 1) :
    klDiv μ uΩ = klDiv π w + klDiv μ (fiberUniformLift d π) := by
  let Ω := Fintype.card (FiberMicrostate d)
  have hμ_uniform :
      klDiv μ uΩ = Real.log Ω - liftEntropy d μ :=
    klDiv_uniform_micro_eq_log_card_sub_entropy d μ uΩ hUniformMicro hμ_sum
  have hπ_uniform :
      klDiv π w = Real.log Ω - liftEntropy d (fiberUniformLift d π) :=
    klDiv_uniform_macro_eq_log_card_sub_liftEntropy d hd π μ w hμ_marginal hUniformPush hμ_sum
  have hledger :
      klDiv μ (fiberUniformLift d π) = liftEntropy d (fiberUniformLift d π) - liftEntropy d μ :=
    paper_pom_kl_defect_identity d hd π μ hμ_marginal hμ_nonneg hπ_nonneg hμ_sum
  calc
    klDiv μ uΩ = Real.log Ω - liftEntropy d μ := hμ_uniform
    _ = (Real.log Ω - liftEntropy d (fiberUniformLift d π)) +
          (liftEntropy d (fiberUniformLift d π) - liftEntropy d μ) := by ring
    _ = klDiv π w + klDiv μ (fiberUniformLift d π) := by rw [hπ_uniform.symm, hledger.symm]

end

end Omega.POM
