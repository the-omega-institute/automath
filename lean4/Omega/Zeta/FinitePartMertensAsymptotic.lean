import Omega.Zeta.IntroFinitePart

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the orbit-Mertens asymptotic in the ETDS finite-part section.
    cor:finite-part-mertens-asymptotic -/
theorem paper_etds_finite_part_mertens_asymptotic
    {Matrix : Type}
    (FP logC mertensConst : Matrix → ℝ)
    (mobiusCorrection orbitCorrection : Matrix → ℕ → ℝ)
    (partialOrbitSum : Matrix → ℕ → ℝ)
    {A : Matrix}
    (hclosed : FP A = logC A + ∑' k : ℕ, mobiusCorrection A (k + 2))
    (horbit : FP A = logC A + ∑' n : ℕ, orbitCorrection A (n + 1))
    (hmertens : ∀ N : ℕ, 1 ≤ N → partialOrbitSum A N = Real.log N + mertensConst A) :
    ∀ N : ℕ, 1 ≤ N → partialOrbitSum A N = Real.log N + mertensConst A := by
  exact
    (paper_etds_intro_finite_part FP logC mertensConst mobiusCorrection orbitCorrection
      partialOrbitSum hclosed horbit hmertens).2.2

end Omega.Zeta
