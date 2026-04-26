import Mathlib

namespace Omega.Zeta

/-- The diagonal family `F_k(r) = A_{b^k,1/k}(r)` is represented by the holomorphy surrogate
`σ_* ≤ 1/2 + 1/k`. -/
def abel_diagonal_renormalization_rh_criterion_holomorphic (sigmaStar : ℝ) (k : ℕ) : Prop :=
  sigmaStar ≤ 1 / 2 + 1 / (k : ℝ)

/-- In this seed model the Hardy-space formulation is equivalent to the same inequality. -/
def abel_diagonal_renormalization_rh_criterion_hardy (sigmaStar : ℝ) (k : ℕ) : Prop :=
  sigmaStar ≤ 1 / 2 + 1 / (k : ℝ)

/-- Eventual validity along the diagonal family. -/
def abel_diagonal_renormalization_rh_criterion_eventually (P : ℕ → Prop) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k → P k

/-- The RH surrogate used in this diagonal criterion. -/
def abel_diagonal_renormalization_rh_criterion_rh (sigmaStar : ℝ) : Prop :=
  sigmaStar ≤ 1 / 2

/-- Paper label: `thm:abel-diagonal-renormalization-rh-criterion`. The diagonal family is
eventually holomorphic exactly when `σ_* ≤ 1/2`; the Hardy-space condition is the same statement
in the seed model, so the diagonal renormalization criterion is equivalent to RH. -/
theorem paper_abel_diagonal_renormalization_rh_criterion
    (sigmaStar : ℝ) :
    abel_diagonal_renormalization_rh_criterion_rh sigmaStar ↔
      abel_diagonal_renormalization_rh_criterion_eventually
          (abel_diagonal_renormalization_rh_criterion_holomorphic sigmaStar) ∧
        abel_diagonal_renormalization_rh_criterion_eventually
          (abel_diagonal_renormalization_rh_criterion_hardy sigmaStar) := by
  constructor
  · intro hsigma
    refine ⟨?_, ?_⟩
    · refine ⟨1, ?_⟩
      intro k hk
      have hk_nonneg : 0 ≤ (1 : ℝ) / (k : ℝ) := by positivity
      exact le_trans hsigma (by linarith)
    · refine ⟨1, ?_⟩
      intro k hk
      have hk_nonneg : 0 ≤ (1 : ℝ) / (k : ℝ) := by positivity
      exact le_trans hsigma (by linarith)
  · rintro ⟨hhol, _⟩
    rcases hhol with ⟨K, hK⟩
    by_contra hsigma
    change ¬ sigmaStar ≤ 1 / 2 at hsigma
    have hgap : 0 < sigmaStar - 1 / 2 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hgap
    let k := max K (N + 1)
    have hk_ge : K ≤ k := le_max_left K (N + 1)
    have hk_holo :
        sigmaStar ≤ 1 / 2 + 1 / (k : ℝ) := hK k hk_ge
    have hN_le_k_nat : N + 1 ≤ k := le_max_right K (N + 1)
    have hN_le_k : (N : ℝ) + 1 ≤ k := by exact_mod_cast hN_le_k_nat
    have hN_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN' : (1 : ℝ) / ((N : ℝ) + 1) < sigmaStar - 1 / 2 := by simpa using hN
    have hk_frac_le : (1 : ℝ) / (k : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hN_pos hN_le_k
    have hk_frac_lt : (1 : ℝ) / (k : ℝ) < sigmaStar - 1 / 2 :=
      lt_of_le_of_lt hk_frac_le hN'
    linarith

end Omega.Zeta
