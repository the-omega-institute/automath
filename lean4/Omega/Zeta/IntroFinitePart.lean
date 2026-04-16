import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the finite-part formula at the Perron pole in the ETDS introduction.
    The theorem packages the determinant correction formula, the primitive-orbit expansion, and the
    corresponding Mertens asymptotic.
    thm:intro-finite-part -/
theorem paper_etds_intro_finite_part
    {Matrix : Type}
    (FP logC mertensConst : Matrix → ℝ)
    (mobiusCorrection orbitCorrection : Matrix → ℕ → ℝ)
    (partialOrbitSum : Matrix → ℕ → ℝ)
    {A : Matrix}
    (hclosed : FP A = logC A + ∑' k : ℕ, mobiusCorrection A (k + 2))
    (horbit : FP A = logC A + ∑' n : ℕ, orbitCorrection A (n + 1))
    (hmertens : ∀ N : ℕ, 1 ≤ N → partialOrbitSum A N = Real.log N + mertensConst A) :
    (FP A = logC A + ∑' k : ℕ, mobiusCorrection A (k + 2)) ∧
    (FP A = logC A + ∑' n : ℕ, orbitCorrection A (n + 1)) ∧
    (∀ N : ℕ, 1 ≤ N → partialOrbitSum A N = Real.log N + mertensConst A) := by
  exact ⟨hclosed, horbit, hmertens⟩

end Omega.Zeta
