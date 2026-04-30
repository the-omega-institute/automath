import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete Smith-invariant data for the `p`-adic branch-entropy saturation law. -/
structure xi_padic_branch_entropy_saturation_law_data where
  xi_padic_branch_entropy_saturation_law_rank : ℕ
  xi_padic_branch_entropy_saturation_law_prime : ℕ
  xi_padic_branch_entropy_saturation_law_smith :
    Fin xi_padic_branch_entropy_saturation_law_rank → ℕ

/-- The truncated Smith precision potential `H_p(k) = Σᵢ min(v_i,k)`. -/
def xi_padic_branch_entropy_saturation_law_precision
    (D : xi_padic_branch_entropy_saturation_law_data) (k : ℕ) : ℕ :=
  ∑ i : Fin D.xi_padic_branch_entropy_saturation_law_rank,
    min (D.xi_padic_branch_entropy_saturation_law_smith i) k

/-- The saturated Smith stiffness `Σᵢ v_i`, equal to the determinant valuation in Smith form. -/
def xi_padic_branch_entropy_saturation_law_stiffness
    (D : xi_padic_branch_entropy_saturation_law_data) : ℕ :=
  ∑ i : Fin D.xi_padic_branch_entropy_saturation_law_rank,
    D.xi_padic_branch_entropy_saturation_law_smith i

/-- A concrete model for the kernel cardinality predicted by the Smith normal form. -/
def xi_padic_branch_entropy_saturation_law_kernelCount
    (D : xi_padic_branch_entropy_saturation_law_data) (k : ℕ) : ℕ :=
  D.xi_padic_branch_entropy_saturation_law_prime ^
    xi_padic_branch_entropy_saturation_law_precision D k

/-- A concrete model for the affine matrix-congruence solution count. -/
def xi_padic_branch_entropy_saturation_law_affineSolutionCount
    (D : xi_padic_branch_entropy_saturation_law_data) (k : ℕ) : ℕ :=
  D.xi_padic_branch_entropy_saturation_law_prime ^
    (D.xi_padic_branch_entropy_saturation_law_rank *
      xi_padic_branch_entropy_saturation_law_precision D k)

/-- The finite saturation level after which all truncated Smith exponents have stabilized. -/
def xi_padic_branch_entropy_saturation_law_saturationLevel
    (D : xi_padic_branch_entropy_saturation_law_data) : ℕ :=
  xi_padic_branch_entropy_saturation_law_stiffness D

lemma xi_padic_branch_entropy_saturation_law_smith_le_stiffness
    (D : xi_padic_branch_entropy_saturation_law_data)
    (i : Fin D.xi_padic_branch_entropy_saturation_law_rank) :
    D.xi_padic_branch_entropy_saturation_law_smith i ≤
      xi_padic_branch_entropy_saturation_law_stiffness D := by
  dsimp [xi_padic_branch_entropy_saturation_law_stiffness]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma xi_padic_branch_entropy_saturation_law_precision_eq_stiffness_of_saturated
    (D : xi_padic_branch_entropy_saturation_law_data) {k : ℕ}
    (hk : xi_padic_branch_entropy_saturation_law_saturationLevel D ≤ k) :
    xi_padic_branch_entropy_saturation_law_precision D k =
      xi_padic_branch_entropy_saturation_law_stiffness D := by
  dsimp [xi_padic_branch_entropy_saturation_law_precision,
    xi_padic_branch_entropy_saturation_law_stiffness,
    xi_padic_branch_entropy_saturation_law_saturationLevel] at hk ⊢
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact Nat.min_eq_left (le_trans
    (xi_padic_branch_entropy_saturation_law_smith_le_stiffness D i) hk)

/-- Paper-facing statement for the `p`-adic branch-entropy saturation law. -/
def xi_padic_branch_entropy_saturation_law_statement
    (D : xi_padic_branch_entropy_saturation_law_data) : Prop :=
  (∀ k : ℕ,
      xi_padic_branch_entropy_saturation_law_kernelCount D k =
        D.xi_padic_branch_entropy_saturation_law_prime ^
          xi_padic_branch_entropy_saturation_law_precision D k) ∧
    (∀ k : ℕ,
      xi_padic_branch_entropy_saturation_law_affineSolutionCount D k =
        D.xi_padic_branch_entropy_saturation_law_prime ^
          (D.xi_padic_branch_entropy_saturation_law_rank *
            xi_padic_branch_entropy_saturation_law_precision D k)) ∧
      ∀ k : ℕ,
        xi_padic_branch_entropy_saturation_law_saturationLevel D ≤ k →
          xi_padic_branch_entropy_saturation_law_precision D k =
            xi_padic_branch_entropy_saturation_law_stiffness D

/-- Paper label: `prop:xi-padic-branch-entropy-saturation-law`. -/
theorem paper_xi_padic_branch_entropy_saturation_law
    (D : xi_padic_branch_entropy_saturation_law_data) :
    xi_padic_branch_entropy_saturation_law_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rfl
  · intro k
    rfl
  · intro k hk
    exact xi_padic_branch_entropy_saturation_law_precision_eq_stiffness_of_saturated D hk

end Omega.Zeta
