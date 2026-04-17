import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The fiber-uniform lift `q̃(a) = q(F(a)) / d(F(a))`. -/
noncomputable def foldUniformLift (F : α → β) (q d : β → ℝ) (a : α) : ℝ :=
  q (F a) / d (F a)

/-- Finite negative log-likelihood risk of the lifted model under `μ`. -/
noncomputable def foldUniformLiftNllRisk (F : α → β) (μ : α → ℝ) (q d : β → ℝ) : ℝ :=
  ∑ a, μ a * (-Real.log (foldUniformLift F q d a))

/-- Cross-entropy of `π` against the fold model `q`. -/
noncomputable def foldCrossEntropy (π q : β → ℝ) : ℝ :=
  ∑ x, π x * (-Real.log (q x))

/-- Shannon entropy of the fold marginal `π`. -/
noncomputable def foldEntropy (π : β → ℝ) : ℝ :=
  ∑ x, π x * (-Real.log (π x))

/-- KL divergence `D_KL(π || q)` written as a finite sum. -/
noncomputable def foldKlDivergence (π q : β → ℝ) : ℝ :=
  ∑ x, π x * Real.log (π x / q x)

/-- Expected logarithmic fiber multiplicity under the fold marginal. -/
noncomputable def foldFiberLogExpectation (π d : β → ℝ) : ℝ :=
  ∑ x, π x * Real.log (d x)

lemma foldCrossEntropy_eq_entropy_add_kl (π q : β → ℝ)
    (hπ : ∀ x, 0 < π x) (hq : ∀ x, 0 < q x) :
    foldCrossEntropy π q = foldEntropy π + foldKlDivergence π q := by
  unfold foldCrossEntropy foldEntropy foldKlDivergence
  calc
    ∑ x, π x * (-Real.log (q x))
        = ∑ x, (π x * (-Real.log (π x)) + π x * Real.log (π x / q x)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [Real.log_div (show π x ≠ 0 by linarith [hπ x]) (show q x ≠ 0 by linarith [hq x])]
            ring
    _ = (∑ x, π x * (-Real.log (π x))) + ∑ x, π x * Real.log (π x / q x) := by
          rw [Finset.sum_add_distrib]
    _ = foldEntropy π + foldKlDivergence π q := by
          simp [foldEntropy, foldKlDivergence]

lemma foldUniformLiftNllRisk_eq_crossEntropy_add_fiberLogExpectation
    (F : α → β) (μ : α → ℝ) (π q d : β → ℝ)
    (hpush : ∀ g : β → ℝ, ∑ a, μ a * g (F a) = ∑ x, π x * g x)
    (hq : ∀ x, 0 < q x) (hd : ∀ x, 0 < d x) :
    foldUniformLiftNllRisk F μ q d = foldCrossEntropy π q + foldFiberLogExpectation π d := by
  unfold foldUniformLiftNllRisk foldUniformLift foldCrossEntropy foldFiberLogExpectation
  calc
    ∑ a, μ a * (-Real.log (q (F a) / d (F a)))
        = ∑ a, μ a * (-Real.log (q (F a))) + ∑ a, μ a * Real.log (d (F a)) := by
            have hsplit :
                ∑ a, μ a * (-Real.log (q (F a) / d (F a))) =
                  ∑ a, (μ a * (-Real.log (q (F a))) + μ a * Real.log (d (F a))) := by
                refine Finset.sum_congr rfl ?_
                intro a ha
                rw [Real.log_div (show q (F a) ≠ 0 by linarith [hq (F a)])
                  (show d (F a) ≠ 0 by linarith [hd (F a)])]
                ring
            rw [hsplit, Finset.sum_add_distrib]
    _ = (∑ x, π x * (-Real.log (q x))) + ∑ x, π x * Real.log (d x) := by
          rw [hpush (fun x => -Real.log (q x)), hpush (fun x => Real.log (d x))]
    _ = foldCrossEntropy π q + foldFiberLogExpectation π d := by
          simp [foldCrossEntropy, foldFiberLogExpectation]

set_option maxHeartbeats 400000 in
/-- Paper-facing negative log-likelihood ledger for the fiber-uniform fold lift. The first
identity is the exact decomposition into entropy, KL, and the fiber logarithm term; the second
rewrites the excess risk over the optimum `q = π` as the KL divergence itself.
    prop:op-algebra-fold-uniformlift-nll-decomposition -/
theorem paper_op_algebra_fold_uniformlift_nll_decomposition
    (F : α → β) (μ : α → ℝ) (π q d : β → ℝ)
    (hpush : ∀ g : β → ℝ, ∑ a, μ a * g (F a) = ∑ x, π x * g x)
    (hπ : ∀ x, 0 < π x) (hq : ∀ x, 0 < q x) (hd : ∀ x, 0 < d x) :
    foldUniformLiftNllRisk F μ q d =
        foldEntropy π + foldKlDivergence π q + foldFiberLogExpectation π d ∧
      foldUniformLiftNllRisk F μ q d =
        foldUniformLiftNllRisk F μ π d + foldKlDivergence π q := by
  have hRisk :
      foldUniformLiftNllRisk F μ q d = foldCrossEntropy π q + foldFiberLogExpectation π d :=
    foldUniformLiftNllRisk_eq_crossEntropy_add_fiberLogExpectation F μ π q d hpush hq hd
  have hCross :
      foldCrossEntropy π q = foldEntropy π + foldKlDivergence π q :=
    foldCrossEntropy_eq_entropy_add_kl π q hπ hq
  have hSelf :
      foldUniformLiftNllRisk F μ π d = foldEntropy π + foldFiberLogExpectation π d := by
    calc
      foldUniformLiftNllRisk F μ π d = foldCrossEntropy π π + foldFiberLogExpectation π d :=
        foldUniformLiftNllRisk_eq_crossEntropy_add_fiberLogExpectation F μ π π d hpush hπ hd
      _ = foldEntropy π + foldFiberLogExpectation π d := by
        rfl
  constructor
  · calc
      foldUniformLiftNllRisk F μ q d = foldCrossEntropy π q + foldFiberLogExpectation π d := hRisk
      _ = foldEntropy π + foldKlDivergence π q + foldFiberLogExpectation π d := by
            rw [hCross]
  · calc
      foldUniformLiftNllRisk F μ q d = foldEntropy π + foldKlDivergence π q +
          foldFiberLogExpectation π d := by
            calc
              foldUniformLiftNllRisk F μ q d =
                  foldCrossEntropy π q + foldFiberLogExpectation π d := hRisk
              _ = foldEntropy π + foldKlDivergence π q + foldFiberLogExpectation π d := by
                    rw [hCross]
      _ = foldUniformLiftNllRisk F μ π d + foldKlDivergence π q := by
            rw [hSelf]
            ring

end

end Omega.OperatorAlgebra
