import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part57eb-oracle-gap-renyi-pressure-upper-bound`. -/
theorem paper_xi_time_part57eb_oracle_gap_renyi_pressure_upper_bound
    {α : Type*} [Fintype α] (d : α → ℕ) (m B q : ℕ) (hq : 1 < q) :
    ((∑ x : α, if (2 ^ B : ℕ) < d x then ((d x : ℝ) - (2 : ℝ)^B) else 0) /
        (2 : ℝ)^m) ≤
      ((∑ x : α, (d x : ℝ)^q) / ((2 : ℝ)^m * (2 : ℝ)^((q - 1) * B))) := by
  let denB : ℝ := (2 : ℝ)^((q - 1) * B)
  let denM : ℝ := (2 : ℝ)^m
  have hdenB_pos : 0 < denB := by
    dsimp [denB]
    positivity
  have hdenM_pos : 0 < denM := by
    dsimp [denM]
    positivity
  have hpoint :
      ∀ x : α,
        (if (2 ^ B : ℕ) < d x then ((d x : ℝ) - (2 : ℝ)^B) else 0) ≤
          (d x : ℝ)^q / denB := by
    intro x
    by_cases hx : (2 ^ B : ℕ) < d x
    · simp [hx]
      have hbase : (2 : ℝ)^B ≤ (d x : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hx)
      have hpow : denB ≤ (d x : ℝ)^(q - 1) := by
        have hmono := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ)^B) hbase (q - 1)
        have hdenB_eq : denB = ((2 : ℝ)^B)^(q - 1) := by
          calc
            denB = (2 : ℝ)^((q - 1) * B) := rfl
            _ = (2 : ℝ)^(B * (q - 1)) := by rw [Nat.mul_comm]
            _ = ((2 : ℝ)^B)^(q - 1) := by rw [pow_mul]
        simpa [hdenB_eq] using hmono
      have hdx_nonneg : 0 ≤ (d x : ℝ) := by positivity
      have hmul : denB * (d x : ℝ) ≤ (d x : ℝ)^q := by
        have hmul' := mul_le_mul_of_nonneg_right hpow hdx_nonneg
        rw [show q = q - 1 + 1 by omega, pow_succ]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
      have hdx_le : (d x : ℝ) ≤ (d x : ℝ)^q / denB := by
        rw [le_div_iff₀ hdenB_pos]
        simpa [mul_comm] using hmul
      have htwo_nonneg : 0 ≤ (2 : ℝ)^B := by positivity
      linarith
    · simp [hx]
      exact div_nonneg (by positivity) (le_of_lt hdenB_pos)
  have hsum :
      (∑ x : α, if (2 ^ B : ℕ) < d x then ((d x : ℝ) - (2 : ℝ)^B) else 0) ≤
        ∑ x : α, (d x : ℝ)^q / denB := by
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hright_sum :
      (∑ x : α, (d x : ℝ)^q / denB) = (∑ x : α, (d x : ℝ)^q) / denB := by
    simp [div_eq_mul_inv, Finset.sum_mul]
  calc
    ((∑ x : α, if (2 ^ B : ℕ) < d x then ((d x : ℝ) - (2 : ℝ)^B) else 0) /
        (2 : ℝ)^m)
        = (∑ x : α, if (2 ^ B : ℕ) < d x then ((d x : ℝ) - (2 : ℝ)^B) else 0) /
            denM := by simp [denM]
    _ ≤ (∑ x : α, (d x : ℝ)^q / denB) / denM := by
      exact div_le_div_of_nonneg_right hsum (le_of_lt hdenM_pos)
    _ = ((∑ x : α, (d x : ℝ)^q) / denB) / denM := by rw [hright_sum]
    _ = ((∑ x : α, (d x : ℝ)^q) / ((2 : ℝ)^m * (2 : ℝ)^((q - 1) * B))) := by
      field_simp [denB, denM, ne_of_gt hdenB_pos, ne_of_gt hdenM_pos]
      ring

end Omega.Zeta
