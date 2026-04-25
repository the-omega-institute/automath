import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Omega.Conclusion.LogRigidityUnderTropical

namespace Omega.Conclusion

private lemma conclusion_prime_weight_log_law_one_zero {δ : ℕ → ℝ}
    (hmul : MultiplicativeOnPos δ) : δ 1 = 0 := by
  have h11 := hmul (a := 1) (b := 1) (by norm_num) (by norm_num)
  linarith

private lemma conclusion_prime_weight_log_law_prime_pow {δ : ℕ → ℝ}
    (hmul : MultiplicativeOnPos δ) :
    ∀ {p k : ℕ}, p.Prime → δ (p ^ k) = (k : ℝ) * δ p := by
  intro p k hp
  induction k with
  | zero =>
      simp [conclusion_prime_weight_log_law_one_zero hmul]
  | succ k ih =>
      have hkpos : 1 ≤ p ^ k := Nat.one_le_pow _ _ (Nat.succ_le_of_lt hp.pos)
      have hppos : 1 ≤ p := Nat.succ_le_of_lt hp.pos
      calc
        δ (p ^ (k + 1)) = δ (p ^ k * p) := by rw [pow_succ]
        _ = δ (p ^ k) + δ p := hmul hkpos hppos
        _ = (k : ℝ) * δ p + δ p := by rw [ih]
        _ = ((k : ℝ) + 1) * δ p := by ring
        _ = ((k + 1 : ℕ) : ℝ) * δ p := by norm_num

private lemma conclusion_prime_weight_log_law_factorization_sum {δ : ℕ → ℝ}
    (hmul : MultiplicativeOnPos δ) :
    ∀ n : ℕ, 1 ≤ n → δ n = n.factorization.sum (fun p k => (k : ℝ) * δ p) := by
  intro n
  induction n using Nat.recOnMul with
  | zero =>
      intro hn
      omega
  | one =>
      intro _
      simp [conclusion_prime_weight_log_law_one_zero hmul]
  | prime p hp =>
      intro _
      simp [Nat.Prime.factorization hp]
  | mul a b ha hb =>
      intro hab
      have ha0 : a ≠ 0 := by
        intro ha'
        simp [ha'] at hab
      have hb0 : b ≠ 0 := by
        intro hb'
        simp [hb'] at hab
      have hapos : 1 ≤ a := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha0)
      have hbpos : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb0)
      calc
        δ (a * b) = δ a + δ b := hmul hapos hbpos
        _ =
            a.factorization.sum (fun p k => (k : ℝ) * δ p) +
              b.factorization.sum (fun p k => (k : ℝ) * δ p) := by
              rw [ha hapos, hb hbpos]
        _ =
            (a.factorization + b.factorization).sum (fun p k => (k : ℝ) * δ p) := by
              rw [Finsupp.sum_add_index']
              · intro p
                simp
              · intro p k₁ k₂
                simp [Nat.cast_add, add_mul]
        _ = (a * b).factorization.sum (fun p k => (k : ℝ) * δ p) := by
              rw [← Nat.factorization_mul ha0 hb0]

/-- Concrete factorization/log-corridor package for prime weights. The multiplicativity hypothesis
expands `δ(n)` as the sum of the prime contributions counted with multiplicity, and the tropical
rigidity theorem specializes to prime inputs without further work. -/
def paper_conclusion_prime_weight_log_law_statement (δ : ℕ → ℝ) (C : ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → δ n = n.factorization.sum (fun p k => (k : ℝ) * δ p)) ∧
    ∀ p : ℕ, p.Prime →
      ((Nat.log2 p : ℝ) * δ 2 - C ≤ δ p) ∧
        (δ p ≤ (Nat.log2 p : ℝ) * δ 2 + ((Nat.log2 p + 1 : ℕ) : ℝ) * C)

/-- Paper label: `cor:conclusion-prime-weight-log-law`. -/
theorem paper_conclusion_prime_weight_log_law (δ : ℕ → ℝ) (C : ℝ)
    (hmul : MultiplicativeOnPos δ) (htrop : TropicalAdditiveWith δ C) (hC : 0 ≤ C)
    (hδ2 : 0 ≤ δ 2) : paper_conclusion_prime_weight_log_law_statement δ C := by
  have hfactor := conclusion_prime_weight_log_law_factorization_sum hmul
  have hcorridor := paper_conclusion_log_rigidity_under_tropical δ C hmul htrop hC hδ2
  refine ⟨hfactor, ?_⟩
  intro p hp
  exact hcorridor.2 p hp.two_le

end Omega.Conclusion
