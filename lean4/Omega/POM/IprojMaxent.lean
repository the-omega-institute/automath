import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import Omega.POM.KLDefectIdentity

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Paper label: `cor:pom-Iproj-maxent`. The entropy of any lift with marginal `π` is bounded above
by the entropy of the fiber-uniform lift, because the corresponding KL defect is nonnegative. -/
theorem paper_pom_iproj_maxent {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) (hμ_nonneg : ∀ a, 0 ≤ μ a)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hμ_sum : Finset.univ.sum μ = 1) :
    liftEntropy d μ ≤ liftEntropy d (fiberUniformLift d π) := by
  have hdefect :
      klDiv μ (fiberUniformLift d π) = liftEntropy d (fiberUniformLift d π) - liftEntropy d μ :=
    paper_pom_kl_defect_identity d hd π μ hμ_marginal hμ_nonneg hπ_nonneg hμ_sum
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
  have hLift_sum : Finset.univ.sum (fiberUniformLift d π) = 1 := by
    calc
      Finset.univ.sum (fiberUniformLift d π) = ∑ x : X, ∑ i : Fin (d x), π x / d x := by
        rw [Fintype.sum_sigma]
        rfl
      _ = ∑ x : X, (d x : ℝ) * (π x / d x) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp
      _ = ∑ x : X, π x := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hd0 : (d x : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (hd x)
        field_simp [hd0]
      _ = 1 := hπ_sum
  have hLift_nonneg : ∀ a, 0 ≤ fiberUniformLift d π a := by
    intro a
    rcases a with ⟨x, i⟩
    exact div_nonneg (hπ_nonneg x) (by exact_mod_cast Nat.zero_le (d x))
  have hkl_nonneg : 0 ≤ klDiv μ (fiberUniformLift d π) := by
    have hterm :
        ∀ a : FiberMicrostate d,
          μ a - fiberUniformLift d π a ≤ μ a * Real.log (μ a / fiberUniformLift d π a) := by
      intro a
      rcases a with ⟨x, i⟩
      by_cases hμ0 : μ ⟨x, i⟩ = 0
      · have hq_nonneg : 0 ≤ fiberUniformLift d π ⟨x, i⟩ := hLift_nonneg ⟨x, i⟩
        simp [hμ0, hq_nonneg]
      · have hq0 : fiberUniformLift d π ⟨x, i⟩ ≠ 0 := by
          intro hq0
          have hd0 : (d x : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (hd x)
          have hπ0 : π x = 0 := by
            have hdiv0 : π x / d x = 0 := by simpa [fiberUniformLift] using hq0
            exact (div_eq_zero_iff.mp hdiv0).resolve_right hd0
          have hx0 : fiberMarginal d μ x = 0 := by
            rw [hμ_marginal x, hπ0]
          have hle : μ ⟨x, i⟩ ≤ fiberMarginal d μ x := by
            simpa [fiberMarginal] using
              (Finset.single_le_sum (fun j _ => hμ_nonneg ⟨x, j⟩) (Finset.mem_univ i))
          rw [hx0] at hle
          have hμzero : μ ⟨x, i⟩ = 0 := by linarith [hμ_nonneg ⟨x, i⟩, hle]
          exact hμ0 hμzero
        have hμ_pos : 0 < μ ⟨x, i⟩ := lt_of_le_of_ne (hμ_nonneg ⟨x, i⟩) (Ne.symm hμ0)
        have hq_pos : 0 < fiberUniformLift d π ⟨x, i⟩ :=
          lt_of_le_of_ne (hLift_nonneg ⟨x, i⟩) (Ne.symm hq0)
        have hlog_le :
            Real.log (fiberUniformLift d π ⟨x, i⟩ / μ ⟨x, i⟩) ≤
              fiberUniformLift d π ⟨x, i⟩ / μ ⟨x, i⟩ - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hq_pos hμ_pos)
        have hlog_ge :
            1 - fiberUniformLift d π ⟨x, i⟩ / μ ⟨x, i⟩ ≤
              Real.log (μ ⟨x, i⟩ / fiberUniformLift d π ⟨x, i⟩) := by
          have hlog_eq :
              Real.log (μ ⟨x, i⟩ / fiberUniformLift d π ⟨x, i⟩) =
                -Real.log (fiberUniformLift d π ⟨x, i⟩ / μ ⟨x, i⟩) := by
            rw [Real.log_div hμ0 hq0, Real.log_div hq0 hμ0]
            ring
          rw [hlog_eq]
          linarith
        have hmul :=
          mul_le_mul_of_nonneg_left hlog_ge (hμ_nonneg ⟨x, i⟩)
        have hleft :
            μ ⟨x, i⟩ * (1 - fiberUniformLift d π ⟨x, i⟩ / μ ⟨x, i⟩) =
              μ ⟨x, i⟩ - fiberUniformLift d π ⟨x, i⟩ := by
          field_simp [hμ0]
        calc
          μ ⟨x, i⟩ - fiberUniformLift d π ⟨x, i⟩
              = μ ⟨x, i⟩ * (1 - fiberUniformLift d π ⟨x, i⟩ / μ ⟨x, i⟩) := by
                  rw [hleft]
          _ ≤ μ ⟨x, i⟩ * Real.log (μ ⟨x, i⟩ / fiberUniformLift d π ⟨x, i⟩) := hmul
    have hsum_le : ∑ a, (μ a - fiberUniformLift d π a) ≤ klDiv μ (fiberUniformLift d π) := by
      simpa [klDiv] using
        (Finset.sum_le_sum fun a _ha => hterm a)
    have hsum_eq_zero : ∑ a, (μ a - fiberUniformLift d π a) = 0 := by
      rw [Finset.sum_sub_distrib, hμ_sum, hLift_sum]
      ring
    have hzero_le : 0 ≤ ∑ a, (μ a - fiberUniformLift d π a) := by
      simp [hsum_eq_zero]
    exact hzero_le.trans hsum_le
  rw [hdefect] at hkl_nonneg
  exact sub_nonneg.mp hkl_nonneg

end

end Omega.POM
