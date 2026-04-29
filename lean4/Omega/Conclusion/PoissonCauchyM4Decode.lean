import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-poisson-cauchy-m4-decode`. -/
theorem paper_conclusion_poisson_cauchy_m4_decode (mu2 mu3 mu4 mu5 mu6 A3 B6 B8 piC : ℝ)
    (hmu2 : mu2 ≠ 0) (hA3 : mu3 ^ 2 = piC ^ 2 * A3 ^ 2)
    (hB6 : B6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32)
    (hB8 :
      B8 =
        (3 * mu2 ^ 4 - 12 * mu2 ^ 2 * mu4 + 9 * mu2 * mu3 ^ 2 + 12 * mu2 * mu6 +
            20 * mu4 ^ 2 - 30 * mu3 * mu5) /
          256) :
    mu4 = mu2 ^ 2 / 8 + 3 * piC ^ 2 * A3 ^ 2 / (4 * mu2) - 8 * B6 / mu2 ∧
      (mu3 = 0 → mu4 = mu2 ^ 2 / 8 - 8 * B6 / mu2) ∧
        (mu3 = 0 →
          mu5 = 0 →
            mu6 =
              (256 * B8 - 3 * mu2 ^ 4 + 12 * mu2 ^ 2 * mu4 - 20 * mu4 ^ 2) /
                (12 * mu2)) := by
  constructor
  · field_simp [hmu2]
    nlinarith [hA3, hB6]
  constructor
  · intro hmu3
    field_simp [hmu2]
    nlinarith [hA3, hB6, hmu3]
  · intro hmu3 hmu5
    have hB8poly :
        256 * B8 =
          3 * mu2 ^ 4 - 12 * mu2 ^ 2 * mu4 + 9 * mu2 * mu3 ^ 2 +
            12 * mu2 * mu6 + 20 * mu4 ^ 2 - 30 * mu3 * mu5 := by
      rw [hB8]
      ring
    have hB8zero :
        256 * B8 =
          3 * mu2 ^ 4 - 12 * mu2 ^ 2 * mu4 + 12 * mu2 * mu6 + 20 * mu4 ^ 2 := by
      rw [hmu3, hmu5] at hB8poly
      simpa using hB8poly
    field_simp [hmu2]
    nlinarith [hB8zero]

end Omega.Conclusion
