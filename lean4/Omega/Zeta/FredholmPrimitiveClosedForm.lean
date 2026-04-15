import Omega.Zeta.ETDSFinitePartPrimitiveClosedForm

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the primitive-orbit closed form in
    `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    thm:finite-part-primitive-closed-form -/
theorem paper_fredholm_witt_finite_part_primitive_closed_form
    {Matrix : Type}
    (FP logC mertensConst : Matrix → ℝ)
    (mobiusCorrection orbitCorrection : Matrix → ℕ → ℝ)
    (partialOrbitSum : Matrix → ℕ → ℝ)
    {A : Matrix}
    (hclosed : FP A = logC A + ∑' k : ℕ, mobiusCorrection A (k + 2))
    (horbit : FP A = logC A + ∑' n : ℕ, orbitCorrection A (n + 1))
    (hmertens : ∀ N : ℕ, 1 ≤ N → partialOrbitSum A N = Real.log N + mertensConst A) :
    (FP A = logC A + ∑' k : ℕ, mobiusCorrection A (k + 2)) ∧
      (FP A = logC A + ∑' n : ℕ, orbitCorrection A (n + 1)) :=
  paper_etds_finite_part_primitive_closed_form
    FP logC mertensConst mobiusCorrection orbitCorrection partialOrbitSum hclosed horbit hmertens

end Omega.Zeta
