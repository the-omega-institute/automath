import Omega.Zeta.IntroFinitePart

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the primitive-orbit closed form in the ETDS finite-part
    section. The Lean core reuses the introduction theorem and extracts the two finite-part
    formulas recorded in the section theorem.
    thm:finite-part-primitive-closed-form -/
theorem paper_etds_finite_part_primitive_closed_form
    {Matrix : Type}
    (FP logC mertensConst : Matrix → ℝ)
    (mobiusCorrection orbitCorrection : Matrix → ℕ → ℝ)
    (partialOrbitSum : Matrix → ℕ → ℝ)
    {A : Matrix}
    (hclosed : FP A = logC A + ∑' k : ℕ, mobiusCorrection A (k + 2))
    (horbit : FP A = logC A + ∑' n : ℕ, orbitCorrection A (n + 1))
    (hmertens : ∀ N : ℕ, 1 ≤ N → partialOrbitSum A N = Real.log N + mertensConst A) :
    (FP A = logC A + ∑' k : ℕ, mobiusCorrection A (k + 2)) ∧
      (FP A = logC A + ∑' n : ℕ, orbitCorrection A (n + 1)) := by
  have hIntro :=
    paper_etds_intro_finite_part FP logC mertensConst mobiusCorrection orbitCorrection
      partialOrbitSum hclosed horbit hmertens
  exact ⟨hIntro.1, hIntro.2.1⟩

end Omega.Zeta
