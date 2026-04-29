import Mathlib.Tactic

namespace Omega.Zeta

/-- The critical positive mode after square-root normalization. -/
def xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaPlus (s : ℝ) :
    ℝ :=
  s ^ (2 : ℕ)

/-- The critical negative mode after square-root normalization. -/
def xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaMinus (s : ℝ) :
    ℝ :=
  -s

/-- A concrete exponential Big-O predicate for scalar remainders. -/
def xi_time_part65_critical_sqrt_mode_first_order_annihilation_isBigO
    (r : ℕ → ℝ) (η : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |r n| ≤ C * η ^ n

/-- The first-order filter `a_{n+1} + s a_n`. -/
def xi_time_part65_critical_sqrt_mode_first_order_annihilation_filter
    (s : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a (n + 1) + s * a n

/-- The transformed remainder after the first-order filter. -/
def xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder
    (s : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  r (n + 1) + s * r n

lemma xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder_bigO
    (s η : ℝ) (r : ℕ → ℝ) (hη : 0 ≤ η)
    (hr : xi_time_part65_critical_sqrt_mode_first_order_annihilation_isBigO r η) :
    xi_time_part65_critical_sqrt_mode_first_order_annihilation_isBigO
      (xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder s r) η := by
  rcases hr with ⟨C, hC, hbound⟩
  refine ⟨C * (η + |s|), ?_, ?_⟩
  · positivity
  intro n
  have hpow_nonneg : 0 ≤ η ^ n := pow_nonneg hη n
  have hnext := hbound (n + 1)
  have hnow := hbound n
  have hnext' : |r (n + 1)| ≤ C * η * η ^ n := by
    calc
      |r (n + 1)| ≤ C * η ^ (n + 1) := hnext
      _ = C * (η * η ^ n) := by rw [pow_succ']
      _ = C * η * η ^ n := by ring
  have hmul_now : |s| * |r n| ≤ |s| * (C * η ^ n) := by
    exact mul_le_mul_of_nonneg_left hnow (abs_nonneg s)
  calc
    |xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder s r n|
        ≤ |r (n + 1)| + |s * r n| := by
          simpa [xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder]
            using abs_add_le (r (n + 1)) (s * r n)
    _ ≤ C * η * η ^ n + |s| * (C * η ^ n) := by
          exact add_le_add hnext' (by simpa [abs_mul] using hmul_now)
    _ = C * (η + |s|) * η ^ n := by ring

/-- Concrete statement for the critical square-root mode one-step annihilation. -/
def xi_time_part65_critical_sqrt_mode_first_order_annihilation_statement : Prop :=
  ∀ (A B s η : ℝ) (a r : ℕ → ℝ),
    0 < s →
      0 ≤ η →
        η < s →
          (∀ n : ℕ,
            a n =
              A * xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaPlus s ^ n +
                B *
                  xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaMinus s ^ n +
                r n) →
            xi_time_part65_critical_sqrt_mode_first_order_annihilation_isBigO r η →
              xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaPlus s =
                  s ^ (2 : ℕ) ∧
                xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaMinus s = -s ∧
                (∀ n : ℕ,
                  xi_time_part65_critical_sqrt_mode_first_order_annihilation_filter s a n =
                    (s ^ (2 : ℕ) + s) * A * s ^ (2 * n) +
                      xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder
                        s r n) ∧
                xi_time_part65_critical_sqrt_mode_first_order_annihilation_isBigO
                  (xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder
                    s r) η

/-- Paper label: `thm:xi-time-part65-critical-sqrt-mode-first-order-annihilation`. -/
theorem paper_xi_time_part65_critical_sqrt_mode_first_order_annihilation :
    xi_time_part65_critical_sqrt_mode_first_order_annihilation_statement := by
  intro A B s η a r hs hη hηs ha hr
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro n
    have hpow : (s ^ (2 : ℕ)) ^ n = s ^ (2 * n) := by
      rw [← pow_mul]
    dsimp [xi_time_part65_critical_sqrt_mode_first_order_annihilation_filter]
    rw [ha (n + 1), ha n]
    simp only [xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaPlus,
      xi_time_part65_critical_sqrt_mode_first_order_annihilation_lambdaMinus,
      xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder]
    rw [hpow]
    have hpow_next : (s ^ (2 : ℕ)) ^ (n + 1) = s ^ (2 * n) * s ^ (2 : ℕ) := by
      rw [pow_succ, hpow]
    rw [hpow_next]
    rw [show (-s) ^ (n + 1) = (-s) ^ n * (-s) by rw [pow_succ]]
    ring
  · exact xi_time_part65_critical_sqrt_mode_first_order_annihilation_filteredRemainder_bigO
      s η r hη hr

end Omega.Zeta
