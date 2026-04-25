import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

def conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_sample_sum
    {n : ℕ} (ω : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i).card

def conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_law
    (p : ℝ) {n : ℕ} (ω : Fin n → Bool) : ℝ :=
  p ^ conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_sample_sum ω *
    (1 - p) ^ (n -
      conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_sample_sum ω)

def conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_balanced_phase_law
    (_θ : Fin 2) {n : ℕ} (ω : Fin n → Bool) : ℝ :=
  conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_law (1 / 2 : ℝ) ω

def conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_balanced_pushforward_mass
    (θ : Fin 2) {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (T : (Fin n → Bool) → α) (t : α) : ℝ :=
  (Finset.univ.filter fun ω => T ω = t).sum
    (conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_balanced_phase_law θ)

def conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_statement : Prop :=
  (∀ n : ℕ, ∀ p q : ℝ, p ≠ q →
    ∃ fp fq : ℕ → ℝ,
      (∀ ω : Fin n → Bool,
        conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_law p ω =
          fp (conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_sample_sum ω)) ∧
      (∀ ω : Fin n → Bool,
        conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_law q ω =
          fq (conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_sample_sum ω))) ∧
    (∀ n : ℕ, ∀ {α : Type*} [Fintype α] [DecidableEq α],
      ∀ T : (Fin n → Bool) → α, ∀ t : α,
        conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_balanced_pushforward_mass
            0 T t =
          conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_balanced_pushforward_mass
            1 T t) ∧
    (∀ k : ℕ, 3 ≤ k →
      let Δ : ℝ := (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1))
      (1 / 2 : ℝ) + Δ ≠ (1 / 2 : ℝ) - Δ)

theorem paper_conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split :
    conclusion_maxfiber_hiddenbit_sufficiency_vs_identifiability_split_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n p q hpq
    refine ⟨fun k => p ^ k * (1 - p) ^ (n - k), fun k => q ^ k * (1 - q) ^ (n - k), ?_, ?_⟩
    · intro ω
      rfl
    · intro ω
      rfl
  · intro n α _ _ T t
    rfl
  · intro k hk
    dsimp
    have hdelta_pos :
        0 < (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1)) := by
      have hfib_num : 0 < Nat.fib (k - 2) := by
        have : 0 < k - 2 := by omega
        exact Nat.fib_pos.mpr this
      have hfib_den : 0 < Nat.fib (k + 1) := Nat.fib_pos.mpr (by omega)
      positivity
    linarith

end

end Omega.Conclusion
