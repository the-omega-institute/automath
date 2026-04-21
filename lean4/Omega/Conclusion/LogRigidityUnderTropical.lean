import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Multiplicativity on positive natural numbers. -/
def MultiplicativeOnPos (δ : ℕ → ℝ) : Prop :=
  ∀ {a b : ℕ}, 1 ≤ a → 1 ≤ b → δ (a * b) = δ a + δ b

/-- Tropical additivity with a uniform additive error on positive natural numbers. -/
def TropicalAdditiveWith (δ : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ {a b : ℕ}, 1 ≤ a → 1 ≤ b → |δ (a + b) - max (δ a) (δ b)| ≤ C

private lemma multiplicative_one_zero {δ : ℕ → ℝ} (hmul : MultiplicativeOnPos δ) : δ 1 = 0 := by
  have h11 := hmul (a := 1) (b := 1) (by norm_num) (by norm_num)
  linarith

/-- Paper label: `thm:conclusion-log-rigidity-under-tropical`.

The multiplicativity hypothesis fixes the exact values on powers of `2`. Tropical additivity then
forces every positive integer to stay within a dyadic logarithmic corridor determined by
`Nat.log2 n`. -/
theorem paper_conclusion_log_rigidity_under_tropical (δ : ℕ → ℝ) (C : ℝ)
    (hmul : MultiplicativeOnPos δ) (htrop : TropicalAdditiveWith δ C) (hC : 0 ≤ C)
    (hδ2 : 0 ≤ δ 2) :
    (∀ k : ℕ, δ (2 ^ k) = (k : ℝ) * δ 2) ∧
      ∀ n : ℕ, 2 ≤ n →
        ((Nat.log2 n : ℝ) * δ 2 - C ≤ δ n) ∧
          (δ n ≤ (Nat.log2 n : ℝ) * δ 2 + ((Nat.log2 n + 1 : ℕ) : ℝ) * C) := by
  have hδ1 : δ 1 = 0 := multiplicative_one_zero hmul
  have hpow2 : ∀ k : ℕ, δ (2 ^ k) = (k : ℝ) * δ 2 := by
    intro k
    induction k with
    | zero =>
        simpa using hδ1
    | succ k ih =>
        have hkpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
        calc
          δ (2 ^ (k + 1)) = δ (2 ^ k * 2) := by rw [pow_succ]
          _ = δ (2 ^ k) + δ 2 := hmul hkpos (by norm_num)
          _ = (k : ℝ) * δ 2 + δ 2 := by rw [ih]
          _ = ((k : ℝ) + 1) * δ 2 := by ring
          _ = ((k + 1 : ℕ) : ℝ) * δ 2 := by norm_num
  have hupper :
      ∀ n : ℕ, 1 ≤ n →
        δ n ≤ (Nat.log2 n : ℝ) * δ 2 + ((Nat.log2 n + 1 : ℕ) : ℝ) * C := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn
    let k := Nat.log2 n
    have hkpow_le : 2 ^ k ≤ n := by
      simpa [k, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp hn)
    let t := n - 2 ^ k
    have hsplit : n = 2 ^ k + t := by
      dsimp [t]
      omega
    by_cases ht : t = 0
    · have hn_eq : n = 2 ^ k := by
        omega
      have hklog : Nat.log2 (2 ^ k) = k := by
        simp [Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]
      rw [hn_eq, hklog, hpow2]
      have hCterm : 0 ≤ ((k + 1 : ℕ) : ℝ) * C := by
        exact mul_nonneg (by positivity) hC
      nlinarith
    · have htpos : 1 ≤ t := by
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht)
      have hn_lt : n < 2 ^ (k + 1) := by
        simpa [k, Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two n
      have ht_lt_pow : t < 2 ^ k := by
        omega
      have ht_lt_n : t < n := by
        omega
      have hIHt :
          δ t ≤ (Nat.log2 t : ℝ) * δ 2 + ((Nat.log2 t + 1 : ℕ) : ℝ) * C := by
        exact ih t ht_lt_n htpos
      have hlogt_lt : Nat.log2 t < k := by
        simpa [Nat.log2_eq_log_two] using
          Nat.log_lt_of_lt_pow (Nat.one_le_iff_ne_zero.mp htpos) ht_lt_pow
      have hmain_t :
          (Nat.log2 t : ℝ) * δ 2 ≤ (k : ℝ) * δ 2 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlogt_lt.le) hδ2
      have herror_t :
          ((Nat.log2 t + 1 : ℕ) : ℝ) * C ≤ (k : ℝ) * C := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.succ_le_of_lt hlogt_lt) hC
      have ht_bound : δ t ≤ (k : ℝ) * δ 2 + (k : ℝ) * C := by
        calc
          δ t ≤ (Nat.log2 t : ℝ) * δ 2 + ((Nat.log2 t + 1 : ℕ) : ℝ) * C := hIHt
          _ ≤ (k : ℝ) * δ 2 + (k : ℝ) * C := add_le_add hmain_t herror_t
      have htrop_n : |δ n - max (δ (2 ^ k)) (δ t)| ≤ C := by
        simpa [hsplit] using
          htrop (a := 2 ^ k) (b := t) (Nat.one_le_pow _ _ (by norm_num)) htpos
      have hk_term :
          δ (2 ^ k) ≤ (k : ℝ) * δ 2 + (k : ℝ) * C := by
        rw [hpow2]
        have hCterm : 0 ≤ (k : ℝ) * C := by
          exact mul_nonneg (by positivity) hC
        nlinarith
      have hmax :
          max (δ (2 ^ k)) (δ t) ≤ (k : ℝ) * δ 2 + (k : ℝ) * C := by
        exact max_le hk_term ht_bound
      have hu : δ n ≤ max (δ (2 ^ k)) (δ t) + C := by
        have hu' : δ n - max (δ (2 ^ k)) (δ t) ≤ C := (abs_le.mp htrop_n).2
        linarith
      calc
        δ n ≤ max (δ (2 ^ k)) (δ t) + C := hu
        _ ≤ ((k : ℝ) * δ 2 + (k : ℝ) * C) + C := add_le_add hmax le_rfl
        _ = (k : ℝ) * δ 2 + ((k : ℝ) + 1) * C := by ring
        _ = (k : ℝ) * δ 2 + ((k + 1 : ℕ) : ℝ) * C := by norm_num
        _ = (Nat.log2 n : ℝ) * δ 2 + ((Nat.log2 n + 1 : ℕ) : ℝ) * C := by
              simp [k]
  refine ⟨hpow2, ?_⟩
  intro n hn
  let k := Nat.log2 n
  let t := n - 2 ^ k
  have hsplit : n = 2 ^ k + t := by
    dsimp [t]
    have hkpow_le : 2 ^ k ≤ n := by
      simpa [k, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    omega
  have hupper_n :
      δ n ≤ (Nat.log2 n : ℝ) * δ 2 + ((Nat.log2 n + 1 : ℕ) : ℝ) * C :=
    hupper n (by omega)
  constructor
  · by_cases ht : t = 0
    · have hn_eq : n = 2 ^ k := by
        omega
      have hklog : Nat.log2 (2 ^ k) = k := by
        simp [Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]
      rw [hn_eq, hklog, hpow2]
      nlinarith
    · have htpos : 1 ≤ t := by
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht)
      have htrop_n : |δ n - max (δ (2 ^ k)) (δ t)| ≤ C := by
        simpa [hsplit] using
          htrop (a := 2 ^ k) (b := t) (Nat.one_le_pow _ _ (by norm_num)) htpos
      have hl : -C ≤ δ n - max (δ (2 ^ k)) (δ t) := (abs_le.mp htrop_n).1
      have hmax_left : δ (2 ^ k) ≤ max (δ (2 ^ k)) (δ t) := le_max_left _ _
      have hk_lower : (k : ℝ) * δ 2 - C ≤ δ n := by
        nlinarith [hl, hmax_left, hpow2 k]
      simpa [k] using hk_lower
  · simpa [k] using hupper_n

end Omega.Conclusion
