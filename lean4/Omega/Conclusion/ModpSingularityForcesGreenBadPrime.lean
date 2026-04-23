import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete local data for the mod-`p` singularity obstruction. The scalar `clearedDet`
represents the determinant of the cleared-denominator matrix. If that determinant is divisible by
the prime `p`, then no integral scalar can invert it to `1`. -/
structure ConclusionModpSingularityForcesGreenBadPrimeData where
  p : ℕ
  hp : Nat.Prime p
  clearedDet : ℕ
  hmodpSingular : p ∣ clearedDet

namespace ConclusionModpSingularityForcesGreenBadPrimeData

/-- The `p`-local obstruction recorded by the conclusion: a mod-`p` singular cleared determinant
cannot admit an integral inverse scalar. -/
def greenBadPrimeForced (data : ConclusionModpSingularityForcesGreenBadPrimeData) : Prop :=
  ∀ m : ℕ, data.clearedDet * m ≠ 1

end ConclusionModpSingularityForcesGreenBadPrimeData

/-- Paper label: `prop:conclusion-modp-singularity-forces-green-bad-prime`. If the cleared
determinant is singular modulo the prime `p`, then it cannot become invertible by multiplying with
an integral `p`-local inverse witness. -/
theorem paper_conclusion_modp_singularity_forces_green_bad_prime
    (data : ConclusionModpSingularityForcesGreenBadPrimeData) : data.greenBadPrimeForced := by
  intro m hm
  have hdiv : data.p ∣ data.clearedDet * m :=
    dvd_mul_of_dvd_left data.hmodpSingular m
  have hdiv_one : data.p ∣ 1 := by
    simpa [hm] using hdiv
  exact data.hp.not_dvd_one hdiv_one

end Omega.Conclusion
