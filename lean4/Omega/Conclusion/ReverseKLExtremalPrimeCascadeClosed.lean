import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

lemma conclusion_reversekl_extremal_prime_cascade_closed_log_geom_sum
    (p : ℕ) (hp : 2 ≤ p) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (ℓ : ℕ) :
    Real.log (1 - x ^ (p ^ (ℓ + 1))) - Real.log (1 - x ^ (p ^ ℓ)) =
      Real.log ((Finset.range p).sum fun k => x ^ (k * p ^ ℓ)) := by
  let y : ℝ := x ^ (p ^ ℓ)
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp_ne : p ≠ 0 := Nat.ne_of_gt hp_pos
  have hpow_ne : p ^ ℓ ≠ 0 := pow_ne_zero ℓ hp_ne
  have hy0 : 0 < y := by
    exact pow_pos hx0 _
  have hy1 : y < 1 := by
    exact pow_lt_one₀ (le_of_lt hx0) hx1 hpow_ne
  have hden : 1 - y ≠ 0 := by nlinarith
  have hyp1 : y ^ p < 1 := pow_lt_one₀ (le_of_lt hy0) hy1 hp_ne
  have hnum : 1 - y ^ p ≠ 0 := by nlinarith
  have hy_pow : y ^ p = x ^ (p ^ (ℓ + 1)) := by
    calc
      y ^ p = x ^ (p ^ ℓ * p) := by simp [y, pow_mul]
      _ = x ^ (p ^ (ℓ + 1)) := by rw [pow_succ]
  have hsum_reindex :
      ((Finset.range p).sum fun k => x ^ (k * p ^ ℓ)) =
        (Finset.range p).sum fun k => y ^ k := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    calc
      x ^ (k * p ^ ℓ) = x ^ (p ^ ℓ * k) := by rw [Nat.mul_comm]
      _ = y ^ k := by simp [y, pow_mul]
  have hgeom : ((Finset.range p).sum fun k => y ^ k) * (1 - y) = 1 - y ^ p := by
    simpa using geom_sum_mul_neg y p
  have hsum_div :
      ((Finset.range p).sum fun k => x ^ (k * p ^ ℓ)) = (1 - y ^ p) / (1 - y) := by
    rw [hsum_reindex]
    exact (eq_div_iff_mul_eq hden).2 hgeom
  calc
    Real.log (1 - x ^ (p ^ (ℓ + 1))) - Real.log (1 - x ^ (p ^ ℓ))
        = Real.log (1 - y ^ p) - Real.log (1 - y) := by rw [hy_pow]
    _ = Real.log ((1 - y ^ p) / (1 - y)) := by rw [Real.log_div hnum hden]
    _ = Real.log ((Finset.range p).sum fun k => x ^ (k * p ^ ℓ)) := by rw [hsum_div]

/-- Paper label: `thm:conclusion-reversekl-extremal-prime-cascade-closed`. -/
theorem paper_conclusion_reversekl_extremal_prime_cascade_closed (p v : ℕ) (hp : 2 ≤ p)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (H G : ℕ → ℝ)
    (hH_flat : ∀ j, j ≤ v → H j = -Real.log (1 - x))
    (hH_tail : ∀ ℓ, H (v + ℓ) = -Real.log (1 - x ^ (p ^ ℓ)))
    (hG : ∀ j, G j = H j - H (j + 1)) :
    (∀ j, j < v → G j = 0) ∧
      ∀ ℓ, G (v + ℓ) = Real.log ((Finset.range p).sum fun k => x ^ (k * p ^ ℓ)) := by
  constructor
  · intro j hj
    rw [hG, hH_flat j (le_of_lt hj), hH_flat (j + 1) (Nat.succ_le_of_lt hj)]
    ring
  · intro ℓ
    rw [hG]
    have hsucc : v + ℓ + 1 = v + (ℓ + 1) := by omega
    rw [hH_tail ℓ, hsucc, hH_tail (ℓ + 1)]
    calc
      -Real.log (1 - x ^ (p ^ ℓ)) - -Real.log (1 - x ^ (p ^ (ℓ + 1)))
          = Real.log (1 - x ^ (p ^ (ℓ + 1))) - Real.log (1 - x ^ (p ^ ℓ)) := by
            ring
      _ = Real.log ((Finset.range p).sum fun k => x ^ (k * p ^ ℓ)) :=
            conclusion_reversekl_extremal_prime_cascade_closed_log_geom_sum p hp x hx0 hx1 ℓ

end Omega.Conclusion
