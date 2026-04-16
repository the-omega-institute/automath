import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.PsiTruncationBounds

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- The finite cyclic-log-zeta truncation over the chosen block set `J`. -/
noncomputable def cyclicLogZetaTruncation {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (multiplicity : ι → Nat) (β : ι → ℝ) (n : ι → Nat) (r : ℝ) : ℝ :=
  ∑ j ∈ J, (multiplicity j : ℝ) * (-Real.log (1 - β j * r ^ (n j)))

/-- The tail left after truncating from `J` down to `J_N`. -/
noncomputable def cyclicLogZetaTailDifference {ι : Type*} [DecidableEq ι]
    (J JN : Finset ι) (multiplicity : ι → Nat) (β : ι → ℝ) (n : ι → Nat) (r : ℝ) : ℝ :=
  ∑ j ∈ (J \ JN), (multiplicity j : ℝ) * (-Real.log (1 - β j * r ^ (n j)))

/-- The Abel-limit tail obtained by sending `r ↑ 1` in the finite-support model. -/
noncomputable def cyclicLogZetaAbelTailDifference {ι : Type*} [DecidableEq ι]
    (J JN : Finset ι) (multiplicity : ι → Nat) (β : ι → ℝ) : ℝ :=
  ∑ j ∈ (J \ JN), (multiplicity j : ℝ) * (-Real.log (1 - β j))

lemma neg_log_one_sub_nonneg (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    0 ≤ -Real.log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hle : 1 - x ≤ 1 := by linarith
  have hlog : Real.log (1 - x) ≤ Real.log 1 := Real.log_le_log hpos hle
  have hlog0 : Real.log (1 - x) ≤ 0 := by simpa using hlog
  linarith

/-- Paper-facing truncation and Abel-tail bound for cyclic log-zeta blocks.
    cor:cyclic-truncation-bounds -/
theorem paper_cyclic_truncation_bounds
    {ι : Type*} [DecidableEq ι]
    (J JN : Finset ι) (multiplicity : ι → Nat) (β : ι → ℝ) (n : ι → Nat) (r : ℝ)
    (hβr : ∀ j ∈ (J \ JN), 0 ≤ β j * r ^ (n j) ∧ β j * r ^ (n j) < 1)
    (hβ : ∀ j ∈ (J \ JN), 0 ≤ β j ∧ β j < 1) :
    0 ≤ cyclicLogZetaTailDifference J JN multiplicity β n r ∧
    cyclicLogZetaTailDifference J JN multiplicity β n r ≤
      ∑ j ∈ (J \ JN), (multiplicity j : ℝ) * (β j * r ^ (n j) / (1 - β j * r ^ (n j))) ∧
    0 ≤ cyclicLogZetaAbelTailDifference J JN multiplicity β ∧
    cyclicLogZetaAbelTailDifference J JN multiplicity β ≤
      ∑ j ∈ (J \ JN), (multiplicity j : ℝ) * (β j / (1 - β j)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cyclicLogZetaTailDifference
    refine sum_nonneg ?_
    intro j hj
    rcases hβr j hj with ⟨hx₀, hx₁⟩
    exact
      mul_nonneg (by exact_mod_cast Nat.zero_le (multiplicity j))
        (neg_log_one_sub_nonneg _ hx₀ hx₁)
  · unfold cyclicLogZetaTailDifference
    refine sum_le_sum ?_
    intro j hj
    rcases hβr j hj with ⟨hx₀, hx₁⟩
    have hbound :
        -Real.log (1 - β j * r ^ (n j)) ≤ β j * r ^ (n j) / (1 - β j * r ^ (n j)) :=
      Omega.Zeta.PsiTruncationBounds.neg_log_one_sub_le_div _ hx₀ hx₁
    exact mul_le_mul_of_nonneg_left hbound (by exact_mod_cast Nat.zero_le (multiplicity j))
  · unfold cyclicLogZetaAbelTailDifference
    refine sum_nonneg ?_
    intro j hj
    rcases hβ j hj with ⟨hx₀, hx₁⟩
    exact
      mul_nonneg (by exact_mod_cast Nat.zero_le (multiplicity j))
        (neg_log_one_sub_nonneg _ hx₀ hx₁)
  · unfold cyclicLogZetaAbelTailDifference
    refine sum_le_sum ?_
    intro j hj
    rcases hβ j hj with ⟨hx₀, hx₁⟩
    have hbound :
        -Real.log (1 - β j) ≤ β j / (1 - β j) :=
      Omega.Zeta.PsiTruncationBounds.neg_log_one_sub_le_div _ hx₀ hx₁
    exact mul_le_mul_of_nonneg_left hbound (by exact_mod_cast Nat.zero_le (multiplicity j))

end Omega.Zeta
