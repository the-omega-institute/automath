import Omega.Conclusion.ModpSingularityForcesGreenBadPrime
import Omega.Conclusion.KirchhoffGreenDeterminantIdentity

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-critical-group-torsion-green-bad-prime-equivalence`.
The nearby Kirchhoff determinant identity file records the bridge from tree torsion to the
cleared-determinant condition; here we package the stored divisibility witness as an `iff`
with the already verified Green bad-prime obstruction. -/
theorem paper_conclusion_critical_group_torsion_green_bad_prime_equivalence
    (data : Omega.Conclusion.ConclusionModpSingularityForcesGreenBadPrimeData) :
    data.p ∣ data.clearedDet ↔
      Omega.Conclusion.ConclusionModpSingularityForcesGreenBadPrimeData.greenBadPrimeForced data := by
  constructor
  · intro _
    exact paper_conclusion_modp_singularity_forces_green_bad_prime data
  · intro _
    exact data.hmodpSingular

end Omega.Conclusion
