import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- Paper-facing uniqueness principle for the Hankel-syndrome inversion polynomial: once two
candidate annihilators are both monic, the divisibility argument in both directions forces the same
minimal polynomial.
    thm:pom-hankel-syndrome-inversion-unique -/
theorem paper_pom_hankel_syndrome_inversion_unique {K : Type*} [Field K] {P Q : K[X]}
    (hP : P.Monic) (hQ : Q.Monic) (hPQ : P ∣ Q) (hQP : Q ∣ P) :
    P = Q := by
  apply Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hPQ
  · exact Polynomial.natDegree_le_of_dvd hQP hP.ne_zero
  · simp [hP.leadingCoeff, hQ.leadingCoeff]

end Omega.POM
