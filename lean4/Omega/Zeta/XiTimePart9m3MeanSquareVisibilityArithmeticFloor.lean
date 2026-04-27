import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

lemma xi_time_part9m3_mean_square_visibility_arithmetic_floor_pointwise (q x : ℕ) :
    (2 * (q : ℤ) + 1) * (x : ℤ) - (q : ℤ) * ((q : ℤ) + 1) ≤ (x : ℤ) ^ 2 := by
  by_cases hx : x ≤ q
  · have hfac :
        0 ≤ ((q : ℤ) - (x : ℤ)) * ((q : ℤ) + 1 - (x : ℤ)) := by
      exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hx))
        (sub_nonneg.mpr (by exact_mod_cast Nat.le_succ_of_le hx))
    nlinarith
  · have hx' : q + 1 ≤ x := Nat.succ_le_of_lt (Nat.lt_of_not_ge hx)
    have hfac :
        0 ≤ ((x : ℤ) - (q : ℤ)) * ((x : ℤ) - (q : ℤ) - 1) := by
      have hxInt : (q : ℤ) + 1 ≤ (x : ℤ) := by exact_mod_cast hx'
      exact mul_nonneg (sub_nonneg.mpr (by linarith))
        (sub_nonneg.mpr (by linarith))
    nlinarith

/-- Paper label: `thm:xi-time-part9m3-mean-square-visibility-arithmetic-floor`. -/
theorem paper_xi_time_part9m3_mean_square_visibility_arithmetic_floor
    {F M : ℕ} (hF : 0 < F) (d : Fin F → ℕ) (hsum : ∑ i, d i = M) :
    (M % F) * (F - M % F) ≤ F * (∑ i, d i ^ 2) - M ^ 2 := by
  classical
  let q := M / F
  let ρ := M % F
  have hρlt : ρ < F := Nat.mod_lt M hF
  have hρle : ρ ≤ F := Nat.le_of_lt hρlt
  have hM : M = F * q + ρ := by
    simpa [q, ρ, Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div M F).symm
  have hsumLower :
      (2 * (q : ℤ) + 1) * (M : ℤ) - (F : ℤ) * (q : ℤ) * ((q : ℤ) + 1) ≤
        ∑ i : Fin F, (d i : ℤ) ^ 2 := by
    have hsumLowerRaw :
        ∑ i : Fin F,
            ((2 * (q : ℤ) + 1) * (d i : ℤ) - (q : ℤ) * ((q : ℤ) + 1)) ≤
          ∑ i : Fin F, (d i : ℤ) ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        xi_time_part9m3_mean_square_visibility_arithmetic_floor_pointwise q (d i)
    have hsumInt : (∑ i : Fin F, (d i : ℤ)) = (M : ℤ) := by
      exact_mod_cast hsum
    calc
      (2 * (q : ℤ) + 1) * (M : ℤ) - (F : ℤ) * (q : ℤ) * ((q : ℤ) + 1) =
          ∑ i : Fin F,
            ((2 * (q : ℤ) + 1) * (d i : ℤ) - (q : ℤ) * ((q : ℤ) + 1)) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumInt]
            simp [Fintype.card_fin]
            ring
      _ ≤ ∑ i : Fin F, (d i : ℤ) ^ 2 := hsumLowerRaw
  have hmul :
      (F : ℤ) *
          ((2 * (q : ℤ) + 1) * (M : ℤ) - (F : ℤ) * (q : ℤ) * ((q : ℤ) + 1)) ≤
        (F : ℤ) * ∑ i : Fin F, (d i : ℤ) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hsumLower (by exact_mod_cast Nat.zero_le F)
  have htargetInt :
      ((ρ * (F - ρ) + M ^ 2 : ℕ) : ℤ) ≤ ((F * (∑ i, d i ^ 2) : ℕ) : ℤ) := by
    have hAlg :
        (F : ℤ) *
            ((2 * (q : ℤ) + 1) * (M : ℤ) - (F : ℤ) * (q : ℤ) * ((q : ℤ) + 1)) =
          (M : ℤ) ^ 2 + (ρ : ℤ) * ((F : ℤ) - (ρ : ℤ)) := by
      rw [hM]
      push_cast
      ring
    have hLeft :
        ((ρ * (F - ρ) + M ^ 2 : ℕ) : ℤ) =
          (M : ℤ) ^ 2 + (ρ : ℤ) * ((F : ℤ) - (ρ : ℤ)) := by
      push_cast [Nat.cast_sub hρle]
      ring
    have hRight :
        ((F * (∑ i, d i ^ 2) : ℕ) : ℤ) =
          (F : ℤ) * ∑ i : Fin F, (d i : ℤ) ^ 2 := by
      simp
    rw [hLeft, hRight, ← hAlg]
    exact hmul
  have htargetNat : ρ * (F - ρ) + M ^ 2 ≤ F * (∑ i, d i ^ 2) := by
    exact_mod_cast htargetInt
  simpa [ρ] using Nat.le_sub_of_add_le htargetNat

end Omega.Zeta
