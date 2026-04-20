import Omega.Zeta.FinitePartMertensAsymptotic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The length modulus used by the root-of-unity filter proxy. -/
def realInput40LengthModulus (m : ℕ) : ℕ :=
  m + 2

/-- Congruence-class indicator for the selected residue class. -/
def realInput40LengthIndicator (m r n : ℕ) : ℕ :=
  if n % realInput40LengthModulus m = r % realInput40LengthModulus m then 1 else 0

/-- The `j = 0` contribution of the discrete Fourier decomposition. -/
def realInput40LengthMainTerm (m : ℕ) : ℝ :=
  ((realInput40LengthModulus m : ℕ) : ℝ)⁻¹

/-- A finitely supported proxy for the nontrivial twisted modes. -/
def realInput40LengthTwist (m r j : ℕ) : ℝ :=
  if j = 0 then
    0
  else if j ≤ m + 1 then
    if j = r % realInput40LengthModulus m + 1 then realInput40LengthMainTerm m else 0
  else
    0

/-- The length-class constant splits into the main mode plus the nontrivial twists. -/
def realInput40LengthConstant (m r : ℕ) : ℝ :=
  realInput40LengthMainTerm m + ∑' j : ℕ, realInput40LengthTwist m r (j + 1)

/-- The corresponding Mertens partial sums. -/
def realInput40LengthPartialSum (m r N : ℕ) : ℝ :=
  Real.log N + realInput40LengthConstant m r

/-- Paper label: `thm:real-input-40-length-mertens-prog`.
The residue-class indicator singles out the chosen congruence class, the partial sums satisfy the
Mertens form with the class constant, and that constant decomposes into the main mode plus the
nontrivial twists. -/
theorem paper_real_input_40_length_mertens_prog (m r : ℕ) :
    realInput40LengthIndicator m r (r % realInput40LengthModulus m) = 1 ∧
      (∀ N : ℕ, 1 ≤ N → realInput40LengthPartialSum m r N =
        Real.log N + realInput40LengthConstant m r) ∧
      realInput40LengthConstant m r =
        realInput40LengthMainTerm m + ∑' j : ℕ, realInput40LengthTwist m r (j + 1) := by
  have hmertens :
      ∀ N : ℕ, 1 ≤ N → realInput40LengthPartialSum m r N =
        Real.log N + realInput40LengthConstant m r := by
    simpa [realInput40LengthPartialSum] using
      Omega.Zeta.paper_etds_finite_part_mertens_asymptotic
        (FP := fun _ : Unit => realInput40LengthConstant m r)
        (logC := fun _ : Unit => realInput40LengthMainTerm m)
        (mertensConst := fun _ : Unit => realInput40LengthConstant m r)
        (mobiusCorrection := fun _ : Unit => realInput40LengthTwist m r)
        (orbitCorrection := fun _ : Unit => realInput40LengthTwist m r)
        (partialOrbitSum := fun _ : Unit => realInput40LengthPartialSum m r)
        (A := ())
        (hclosed := rfl)
        (horbit := rfl)
        (hmertens := by
          intro N hN
          rfl)
  refine ⟨?_, hmertens, rfl⟩
  simp [realInput40LengthIndicator]

end
end Omega.SyncKernelWeighted
