import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-deep-toeplitz-negative-gap-det-tr-geometry`. -/
theorem paper_xi_deep_toeplitz_negative_gap_det_tr_geometry {k : Nat} (hk : 2 <= k)
    {tr det lambdaMin : Real} (htr : 0 < tr)
    (hprod : det <= lambdaMin * (tr / (k - 1 : Real)) ^ (k - 1)) :
    ((k - 1 : Real) ^ (k - 1) / tr ^ (k - 1)) * det <= lambdaMin := by
  have hkreal : (2 : Real) ≤ k := by exact_mod_cast hk
  have hkpos : 0 < (k : Real) - 1 := by linarith
  have hscale_pos : 0 < (k - 1 : Real) ^ (k - 1) / tr ^ (k - 1) := by
    exact div_pos (pow_pos hkpos _) (pow_pos htr _)
  have hscaled :=
    mul_le_mul_of_nonneg_left hprod (le_of_lt hscale_pos)
  calc
    ((k - 1 : Real) ^ (k - 1) / tr ^ (k - 1)) * det
        ≤ ((k - 1 : Real) ^ (k - 1) / tr ^ (k - 1)) *
            (lambdaMin * (tr / (k - 1 : Real)) ^ (k - 1)) := hscaled
    _ = lambdaMin := by
      have hkpow_ne : ((k : Real) - 1) ^ (k - 1) ≠ 0 :=
        pow_ne_zero _ (ne_of_gt hkpos)
      have htrpow_ne : tr ^ (k - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt htr)
      rw [div_pow]
      field_simp [hkpow_ne, htrpow_ne, ne_of_gt hkpos, ne_of_gt htr]

end Omega.Zeta
