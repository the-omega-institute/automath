import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Paper label: `thm:pom-multiplicative-refinement-telescope-alpha`. A concrete core package for
the multiplicative refinement chain: the one-step difference formula coming from the
multiplicative factorization identity, together with the resulting antitonicity under
nonnegativity of the escort entropy loss. -/
def pom_multiplicative_refinement_telescope_alpha_statement : Prop :=
  ∀ (P : ℕ → ℝ) (hEsc : ℕ → ℕ → ℝ) (a b : ℕ),
    1 ≤ a →
    2 ≤ b →
    (∀ n : ℕ,
      P (a * b ^ (n + 1)) =
        (b : ℝ) * P (a * b ^ n) - ((b : ℝ) - 1) * hEsc (a * b ^ n) b) →
    (∀ n : ℕ, 0 ≤ hEsc (a * b ^ n) b) →
    let α : ℕ → ℝ := fun n => P (a * b ^ n) / ((a * b ^ n : ℕ) : ℝ)
    let Δ : ℕ → ℝ := fun n =>
      (((b : ℝ) - 1) * hEsc (a * b ^ n) b) / (((a * b ^ (n + 1) : ℕ) : ℝ))
    (∀ n : ℕ, α n - α (n + 1) = Δ n) ∧ Antitone α

theorem paper_pom_multiplicative_refinement_telescope_alpha :
    pom_multiplicative_refinement_telescope_alpha_statement := by
  intro P hEsc a b ha hb hfac hnonneg
  let α : ℕ → ℝ := fun n => P (a * b ^ n) / ((a * b ^ n : ℕ) : ℝ)
  let Δ : ℕ → ℝ := fun n =>
    (((b : ℝ) - 1) * hEsc (a * b ^ n) b) / (((a * b ^ (n + 1) : ℕ) : ℝ))
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hb
  have hbminus : 0 ≤ (b : ℝ) - 1 := by
    have hb2R : (2 : ℝ) ≤ b := by
      exact_mod_cast hb
    linarith
  have hΔeq : ∀ n : ℕ, α n - α (n + 1) = Δ n := by
    intro n
    dsimp [α, Δ]
    have hcast :
        (((a * b ^ (n + 1) : ℕ) : ℝ)) = (b : ℝ) * (((a * b ^ n : ℕ) : ℝ)) := by
      norm_num [Nat.cast_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm]
    rw [hfac n, hcast]
    field_simp [haR.ne', hbR.ne', Nat.cast_mul]
    ring
  have hαanti : Antitone α := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hstep : 0 ≤ α n - α (n + 1) := by
      rw [hΔeq n]
      exact div_nonneg (mul_nonneg hbminus (hnonneg n)) (by positivity)
    linarith
  exact ⟨hΔeq, hαanti⟩

end

end Omega.POM
