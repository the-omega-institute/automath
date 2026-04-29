import Omega.POM.KLDefectIdentity

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

open Omega.POM

section XiNullFiberEntropyWindow

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The visible entropy of the fixed macro-marginal `π`. -/
noncomputable def xiNullFiberBaseEntropy (π : X → ℝ) : ℝ :=
  ∑ x : X, Real.negMulLog (π x)

/-- The fiber-capacity term `κ_m(π) = E_π[log d(X)]` for the explicit finite-fiber model. -/
noncomputable def xiNullFiberKappa (d : X → ℕ) (π : X → ℝ) : ℝ :=
  ∑ x : X, π x * Real.log (d x)

/-- The distinguished section chooses the `0`-th point in every nonempty fiber. -/
def xiNullFiberSectionIndex (d : X → ℕ) (hd : ∀ x, 0 < d x) (x : X) : Fin (d x) :=
  ⟨0, hd x⟩

/-- The section lift places all of the macro-mass `π x` on the distinguished point of the
fiber above `x`. -/
noncomputable def xiNullFiberSectionLift (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) :
    FiberMicrostate d → ℝ
  | ⟨x, i⟩ => if i = xiNullFiberSectionIndex d hd x then π x else 0

lemma xiNullFiberUniformLift_marginal (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) :
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

lemma xiNullFiberPi_sum_eq_one (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
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

lemma xiNullFiberSectionLift_marginal (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) :
    ∀ x, fiberMarginal d (xiNullFiberSectionLift d hd π) x = π x := by
  intro x
  unfold fiberMarginal xiNullFiberSectionLift
  rw [Finset.sum_eq_single (xiNullFiberSectionIndex d hd x)]
  · simp [xiNullFiberSectionIndex]
  · intro i _ hne
    by_cases hi : i = xiNullFiberSectionIndex d hd x
    · exact False.elim (hne hi)
    · simpa [xiNullFiberSectionLift, hi]
  · intro hnot
    simp at hnot

lemma xiNullFiberSectionLift_nonneg (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ)
    (hπ_nonneg : ∀ x, 0 ≤ π x) : ∀ a, 0 ≤ xiNullFiberSectionLift d hd π a := by
  rintro ⟨x, i⟩
  by_cases hi : i = xiNullFiberSectionIndex d hd x
  · simp [xiNullFiberSectionLift, hi, hπ_nonneg x]
  · simp [xiNullFiberSectionLift, hi]

lemma xiNullFiberSectionLift_sum (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ)
    (hπ_sum : Finset.univ.sum π = 1) :
    Finset.univ.sum (xiNullFiberSectionLift d hd π) = 1 := by
  rw [Fintype.sum_sigma]
  calc
    ∑ x : X, ∑ i : Fin (d x), xiNullFiberSectionLift d hd π ⟨x, i⟩
        = ∑ x : X, π x := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact xiNullFiberSectionLift_marginal d hd π x
    _ = 1 := hπ_sum

lemma xiNullFiberSectionLift_entropy (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) :
    liftEntropy d (xiNullFiberSectionLift d hd π) = xiNullFiberBaseEntropy π := by
  unfold liftEntropy xiNullFiberBaseEntropy fiberEntropy xiNullFiberSectionLift
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [Finset.sum_eq_single (xiNullFiberSectionIndex d hd x)]
  · simp [xiNullFiberSectionIndex]
  · intro i _ hne
    by_cases hi : i = xiNullFiberSectionIndex d hd x
    · exact False.elim (hne hi)
    · simpa [xiNullFiberSectionLift, hi]
  · intro hnot
    simp at hnot

/-- Paper label: `thm:xi-null-fiber-entropy-window`. For a fixed macro-marginal `π`, the entropy
ledger is the POM KL identity specialized to the explicit finite fibers; the fiber-uniform lift
realizes the upper endpoint and the section lift realizes the lower endpoint. -/
theorem paper_xi_null_fiber_entropy_window (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ)
    (μ : FiberMicrostate d → ℝ) (hμ_marginal : ∀ x, fiberMarginal d μ x = π x)
    (hμ_nonneg : ∀ a, 0 ≤ μ a) (hπ_nonneg : ∀ x, 0 ≤ π x) (hμ_sum : Finset.univ.sum μ = 1) :
    liftEntropy d μ =
        xiNullFiberBaseEntropy π + xiNullFiberKappa d π -
          klDiv μ (fiberUniformLift d π) ∧
      liftEntropy d (fiberUniformLift d π) =
        xiNullFiberBaseEntropy π + xiNullFiberKappa d π ∧
      liftEntropy d (xiNullFiberSectionLift d hd π) = xiNullFiberBaseEntropy π ∧
      klDiv (xiNullFiberSectionLift d hd π) (fiberUniformLift d π) = xiNullFiberKappa d π := by
  have hledger := paper_pom_kl_ledger d hd π μ hμ_marginal hμ_nonneg hπ_nonneg hμ_sum
  have huniform_entropy :
      liftEntropy d (fiberUniformLift d π) = xiNullFiberBaseEntropy π + xiNullFiberKappa d π := by
    simpa [xiNullFiberBaseEntropy, xiNullFiberKappa] using
      (paper_pom_maxent_lift d hd π (fiberUniformLift d π)
        (by intro x i j; rfl) (xiNullFiberUniformLift_marginal d hd π)).2
  have hπ_sum : Finset.univ.sum π = 1 :=
    xiNullFiberPi_sum_eq_one d π μ hμ_marginal hμ_sum
  have hsection_entropy :
      liftEntropy d (xiNullFiberSectionLift d hd π) = xiNullFiberBaseEntropy π :=
    xiNullFiberSectionLift_entropy d hd π
  have hsection_defect :
      klDiv (xiNullFiberSectionLift d hd π) (fiberUniformLift d π) =
        liftEntropy d (fiberUniformLift d π) - liftEntropy d (xiNullFiberSectionLift d hd π) :=
    paper_pom_kl_defect_identity d hd π (xiNullFiberSectionLift d hd π)
      (xiNullFiberSectionLift_marginal d hd π)
      (xiNullFiberSectionLift_nonneg d hd π hπ_nonneg) hπ_nonneg
      (xiNullFiberSectionLift_sum d hd π hπ_sum)
  have hsection_kl :
      klDiv (xiNullFiberSectionLift d hd π) (fiberUniformLift d π) = xiNullFiberKappa d π := by
    calc
      klDiv (xiNullFiberSectionLift d hd π) (fiberUniformLift d π)
          = liftEntropy d (fiberUniformLift d π) -
              liftEntropy d (xiNullFiberSectionLift d hd π) := hsection_defect
      _ = (xiNullFiberBaseEntropy π + xiNullFiberKappa d π) - xiNullFiberBaseEntropy π := by
            rw [huniform_entropy, hsection_entropy]
      _ = xiNullFiberKappa d π := by ring
  refine ⟨?_, huniform_entropy, hsection_entropy, hsection_kl⟩
  simpa [xiNullFiberBaseEntropy, xiNullFiberKappa] using hledger

end XiNullFiberEntropyWindow

end

end Omega.Zeta
