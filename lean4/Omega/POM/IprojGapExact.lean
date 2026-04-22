import Mathlib.Tactic
import Omega.POM.KLPythagorasUniform

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Paper label: `cor:pom-Iproj-gap-exact`. -/
theorem paper_pom_iproj_gap_exact (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ)
    (μ : FiberMicrostate d → ℝ) (uΩ : FiberMicrostate d → ℝ) (w : X → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) (hUniformMicro :
      ∀ a, uΩ a = (1 : ℝ) / Fintype.card (FiberMicrostate d))
    (hUniformPush : ∀ x, w x = (d x : ℝ) / Fintype.card (FiberMicrostate d))
    (hμ_nonneg : ∀ a, 0 ≤ μ a) (hπ_nonneg : ∀ x, 0 ≤ π x) (hμ_sum : Finset.univ.sum μ = 1) :
    klDiv μ uΩ - klDiv (fiberUniformLift d π) uΩ = klDiv μ (fiberUniformLift d π) := by
  have hmain :
      klDiv μ uΩ = klDiv π w + klDiv μ (fiberUniformLift d π) :=
    paper_pom_kl_pythagoras_uniform d hd π μ uΩ w hμ_marginal hUniformMicro hUniformPush
      hμ_nonneg hπ_nonneg hμ_sum
  have hLiftMarginal : ∀ x, fiberMarginal d (fiberUniformLift d π) x = π x := by
    intro x
    have hd0 : (d x : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (hd x)
    calc
      fiberMarginal d (fiberUniformLift d π) x = ∑ _i : Fin (d x), π x / d x := by
        simp [fiberMarginal, fiberUniformLift]
      _ = (d x : ℝ) * (π x / d x) := by simp
      _ = π x := by
        field_simp [hd0]
  have hπ_sum : Finset.univ.sum π = 1 := by
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
  have hLift_nonneg : ∀ a, 0 ≤ fiberUniformLift d π a := by
    intro a
    rcases a with ⟨x, i⟩
    exact div_nonneg (hπ_nonneg x) (by exact_mod_cast Nat.zero_le (d x))
  have hLift_sum : Finset.univ.sum (fiberUniformLift d π) = 1 := by
    calc
      Finset.univ.sum (fiberUniformLift d π) =
          ∑ x : X, fiberMarginal d (fiberUniformLift d π) x := by
            rw [Fintype.sum_sigma]
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [fiberMarginal]
      _ = Finset.univ.sum π := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [hLiftMarginal x]
      _ = 1 := hπ_sum
  have hLift_self :
      klDiv (fiberUniformLift d π) (fiberUniformLift d π) = 0 := by
    simpa using
      (paper_pom_kl_defect_identity d hd π (fiberUniformLift d π) hLiftMarginal hLift_nonneg
        hπ_nonneg hLift_sum)
  have hLift_uniform :
      klDiv (fiberUniformLift d π) uΩ = klDiv π w := by
    have hLift_main :
        klDiv (fiberUniformLift d π) uΩ =
          klDiv π w + klDiv (fiberUniformLift d π) (fiberUniformLift d π) :=
      paper_pom_kl_pythagoras_uniform d hd π (fiberUniformLift d π) uΩ w hLiftMarginal
        hUniformMicro hUniformPush hLift_nonneg hπ_nonneg hLift_sum
    simpa [hLift_self] using hLift_main
  calc
    klDiv μ uΩ - klDiv (fiberUniformLift d π) uΩ =
        (klDiv π w + klDiv μ (fiberUniformLift d π)) - klDiv (fiberUniformLift d π) uΩ := by
          rw [hmain]
    _ = (klDiv π w + klDiv μ (fiberUniformLift d π)) - klDiv π w := by
          rw [hLift_uniform]
    _ = klDiv μ (fiberUniformLift d π) := by
          ring

end

end Omega.POM
