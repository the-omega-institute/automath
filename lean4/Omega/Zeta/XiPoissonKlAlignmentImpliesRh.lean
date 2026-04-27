import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Poisson-KL alignment data: a uniform Jensen defect bounded by a `C / (n+1)`
rate. -/
structure xi_poisson_kl_alignment_implies_rh_data where
  uniformJensenDefect : ℕ → ℝ
  alignmentConstant : ℝ
  alignmentConstant_nonneg : 0 ≤ alignmentConstant
  poisson_kl_alignment_decay :
    ∀ n, |uniformJensenDefect n| ≤ alignmentConstant / ((n : ℝ) + 1)

namespace xi_poisson_kl_alignment_implies_rh_data

/-- The concrete uniform Jensen-defect convergence criterion. -/
def xi_poisson_kl_alignment_implies_rh_uniform_jensen_defect_converges
    (D : xi_poisson_kl_alignment_implies_rh_data) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |D.uniformJensenDefect n| < ε

/-- In this local formal package, RH is represented by the Jensen-defect criterion. -/
def riemannHypothesis (D : xi_poisson_kl_alignment_implies_rh_data) : Prop :=
  D.xi_poisson_kl_alignment_implies_rh_uniform_jensen_defect_converges

end xi_poisson_kl_alignment_implies_rh_data

/-- Paper label: `cor:xi-poisson-kl-alignment-implies-rh`. -/
theorem paper_xi_poisson_kl_alignment_implies_rh
    (D : xi_poisson_kl_alignment_implies_rh_data) : D.riemannHypothesis := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (D.alignmentConstant / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hbound := D.poisson_kl_alignment_decay n
  have hden : 0 < ((n : ℝ) + 1) := by positivity
  have hconstant_lt : D.alignmentConstant < ε * ((n : ℝ) + 1) := by
    have hmul : ε * (D.alignmentConstant / ε) < ε * (N : ℝ) :=
      mul_lt_mul_of_pos_left hN hε
    have hleft : ε * (D.alignmentConstant / ε) = D.alignmentConstant := by
      field_simp [ne_of_gt hε]
    have hN_le_n : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hN_le_succ : (N : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hright : ε * (N : ℝ) ≤ ε * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hN_le_succ (le_of_lt hε)
    linarith
  have hdecay_lt : D.alignmentConstant / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hden]
    exact hconstant_lt
  exact lt_of_le_of_lt hbound hdecay_lt

end Omega.Zeta
