import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-lucas-quadratic-factorization`. -/
theorem paper_conclusion_lucas_quadratic_factorization
    (q k : ℕ) (α β P Δ : ℤ) (L F : ℕ → ℤ) (hk : 2 * k ≤ q)
    (hP : α * β = P) (hPunit : P ^ 2 = 1)
    (hL : ∀ n, L n = α ^ n + β ^ n)
    (hDisc : ∀ n, L n ^ 2 - Δ * F n ^ 2 = 4 * P ^ n) :
    (α ^ (q - k) * β ^ k + α ^ k * β ^ (q - k) = P ^ k * L (q - 2 * k)) ∧
      ((P ^ k * L (q - 2 * k)) ^ 2 - 4 * P ^ q =
        Δ * F (q - 2 * k) ^ 2) := by
  let n := q - 2 * k
  have hqk : q - k = k + n := by
    dsimp [n]
    omega
  have hq : q = 2 * k + n := by
    dsimp [n]
    omega
  have hP2k : P ^ (2 * k) = 1 := by
    calc
      P ^ (2 * k) = (P ^ 2) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hPunit, one_pow]
  have hPk_mul : P ^ k * P ^ k = 1 := by
    calc
      P ^ k * P ^ k = P ^ (k + k) := by rw [← pow_add]
      _ = P ^ (2 * k) := by congr 1; omega
      _ = 1 := hP2k
  have hPq : P ^ q = P ^ n := by
    calc
      P ^ q = P ^ (2 * k + n) := by rw [hq]
      _ = P ^ (2 * k) * P ^ n := by rw [pow_add]
      _ = P ^ n := by rw [hP2k, one_mul]
  have hleft : α ^ (q - k) * β ^ k = P ^ k * α ^ n := by
    calc
      α ^ (q - k) * β ^ k = (α ^ k * α ^ n) * β ^ k := by rw [hqk, pow_add]
      _ = (α * β) ^ k * α ^ n := by
        rw [mul_pow]
        ring
      _ = P ^ k * α ^ n := by rw [hP]
  have hright : α ^ k * β ^ (q - k) = P ^ k * β ^ n := by
    calc
      α ^ k * β ^ (q - k) = α ^ k * (β ^ k * β ^ n) := by rw [hqk, pow_add]
      _ = (α * β) ^ k * β ^ n := by
        rw [mul_pow]
        ring
      _ = P ^ k * β ^ n := by rw [hP]
  constructor
  · calc
      α ^ (q - k) * β ^ k + α ^ k * β ^ (q - k) =
          P ^ k * α ^ n + P ^ k * β ^ n := by rw [hleft, hright]
      _ = P ^ k * L n := by rw [hL n]; ring
  · have hdisc : L n ^ 2 - 4 * P ^ n = Δ * F n ^ 2 := by
      nlinarith [hDisc n]
    calc
      (P ^ k * L n) ^ 2 - 4 * P ^ q = (P ^ k * P ^ k) * L n ^ 2 - 4 * P ^ q := by
        ring
      _ = L n ^ 2 - 4 * P ^ n := by rw [hPk_mul, hPq]; ring
      _ = Δ * F n ^ 2 := hdisc

end Omega.Conclusion
