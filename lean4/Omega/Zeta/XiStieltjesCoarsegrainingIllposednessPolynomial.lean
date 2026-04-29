import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-stieltjes-coarsegraining-illposedness-polynomial`. -/
theorem paper_xi_stieltjes_coarsegraining_illposedness_polynomial
    (kappa : Nat) (sep L : Nat → Real) (C K : Real) (_hkappa : 1 ≤ kappa) (hC : 0 < C)
    (hK : 0 < K) (hsep_pos : ∀ t, 0 < sep t)
    (hsep_le : ∀ t, sep t ≤ C / ((t : Real) + 1) ^ 2)
    (hcond : ∀ t, K / (sep t) ^ (kappa - 1) ≤ L t) :
    ∃ A > 0, ∀ t : Nat, A * ((t : Real) + 1) ^ (2 * (kappa - 1)) ≤ L t := by
  let n := kappa - 1
  refine ⟨K / C ^ n, div_pos hK (pow_pos hC n), ?_⟩
  intro t
  let x : Real := (t : Real) + 1
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hsep_pow_pos : 0 < (sep t) ^ n := pow_pos (hsep_pos t) n
  have hsep_pow_le : (sep t) ^ n ≤ (C / x ^ 2) ^ n := by
    exact pow_le_pow_left₀ (le_of_lt (hsep_pos t)) (by simpa [x] using hsep_le t) n
  have hfactor_nonneg : 0 ≤ K / C ^ n := le_of_lt (div_pos hK (pow_pos hC n))
  have hxpow_nonneg : 0 ≤ x ^ (2 * n) := pow_nonneg (le_of_lt hx) _
  have hscaled :
      (K / C ^ n * x ^ (2 * n)) * (sep t) ^ n ≤ K := by
    calc
      (K / C ^ n * x ^ (2 * n)) * (sep t) ^ n
          = (K / C ^ n) * (x ^ (2 * n) * (sep t) ^ n) := by ring
      _ ≤ (K / C ^ n) * (x ^ (2 * n) * (C / x ^ 2) ^ n) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsep_pow_le hxpow_nonneg) hfactor_nonneg
      _ = (K / C ^ n) * C ^ n := by
        congr 1
        calc
          x ^ (2 * n) * (C / x ^ 2) ^ n = (x ^ 2) ^ n * (C / x ^ 2) ^ n := by
            rw [pow_mul]
          _ = (x ^ 2 * (C / x ^ 2)) ^ n := by rw [← mul_pow]
          _ = C ^ n := by
            have hx2_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hx)
            field_simp [hx2_ne]
      _ = K := by
        field_simp [pow_ne_zero n (ne_of_gt hC)]
  have hlower : K / C ^ n * x ^ (2 * n) ≤ K / (sep t) ^ n := by
    exact (le_div_iff₀ hsep_pow_pos).2 hscaled
  exact le_trans (by simpa [n, x] using hlower) (hcond t)

end Omega.Zeta
