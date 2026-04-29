import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-p7-leyang-inversion-recovers-chebotarev-densities`. -/
theorem paper_xi_p7_leyang_inversion_recovers_chebotarev_densities
    (mu4_neg1 mu5_zeta5 mu5_i mu5_zeta6 mu5_zeta3 mu5_neg1 : ℚ) :
    ∃! d : Fin 7 → ℚ,
      d 6 = 5 * mu5_zeta5 ∧
        d 5 = 5 * mu5_i ∧
          d 4 = 5 * mu5_zeta6 ∧
            d 3 = (5 * mu5_zeta3 - d 4) / 2 ∧
              d 2 =
                  (4 * mu4_neg1 - d 4 - d 5) - ((5 / 2) * mu5_neg1 - d 5) ∧
                d 1 =
                    2 * ((5 / 2) * mu5_neg1 - d 5) -
                      (4 * mu4_neg1 - d 4 - d 5) ∧
                  d 0 = 1 - (d 1 + d 2 + d 3 + d 4 + d 5 + d 6) := by
  let x6 : ℚ := 5 * mu5_zeta5
  let x5 : ℚ := 5 * mu5_i
  let x4 : ℚ := 5 * mu5_zeta6
  let x3 : ℚ := (5 * mu5_zeta3 - x4) / 2
  let x2 : ℚ := (4 * mu4_neg1 - x4 - x5) - ((5 / 2) * mu5_neg1 - x5)
  let x1 : ℚ := 2 * ((5 / 2) * mu5_neg1 - x5) - (4 * mu4_neg1 - x4 - x5)
  let x0 : ℚ := 1 - (x1 + x2 + x3 + x4 + x5 + x6)
  let d : Fin 7 → ℚ := ![x0, x1, x2, x3, x4, x5, x6]
  refine ⟨d, ?_, ?_⟩
  · simp [d, x0, x1, x2, x3, x4, x5, x6]
  · intro e he
    rcases he with ⟨h6, h5, h4, h3, h2, h1, h0⟩
    have h6' : e 6 = x6 := by simpa [x6] using h6
    have h5' : e 5 = x5 := by simpa [x5] using h5
    have h4' : e 4 = x4 := by simpa [x4] using h4
    have h3' : e 3 = x3 := by
      rw [h3, h4']
    have h2' : e 2 = x2 := by
      rw [h2, h4', h5']
    have h1' : e 1 = x1 := by
      rw [h1, h4', h5']
    have h0' : e 0 = x0 := by
      rw [h0, h1', h2', h3', h4', h5', h6']
    funext i
    fin_cases i
    · simpa [d] using h0'
    · simpa [d] using h1'
    · simpa [d] using h2'
    · simpa [d] using h3'
    · simpa [d] using h4'
    · simpa [d] using h5'
    · simpa [d] using h6'

end Omega.Zeta
