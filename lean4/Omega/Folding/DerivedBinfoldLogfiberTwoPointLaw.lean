import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinTwoPointLimitLaw

namespace Omega.Folding

/-- The two atoms of the limiting scaled log-fiber law. -/
noncomputable def derivedBinfoldLogfiberAtom (b : Bool) : ℝ :=
  if b then Real.log Real.goldenRatio else 0

/-- The limiting masses are the last-bit two-point masses from the bin-fold law. -/
noncomputable def derivedBinfoldLogfiberLimitMass (b : Bool) : ℝ :=
  foldBinTwoAtomLimitMass b

/-- Moment generating function of the limiting two-point log-fiber law. -/
noncomputable def derivedBinfoldLogfiberLimitMgf (t : ℝ) : ℝ :=
  derivedBinfoldLogfiberLimitMass false +
    derivedBinfoldLogfiberLimitMass true * Real.goldenRatio ^ t

/-- Concrete package for the derived log-fiber two-point law: the underlying bin-fold two-point
law holds, the atoms are `0` and `log φ`, the masses are explicit, and the mgf is closed form. -/
def derivedBinfoldLogfiberTwoPointLaw (D : FoldBinTwoStateAsymptoticData) : Prop :=
  paper_fold_bin_two_point_limit_law_statement D ∧
    derivedBinfoldLogfiberAtom false = 0 ∧
    derivedBinfoldLogfiberAtom true = Real.log Real.goldenRatio ∧
    derivedBinfoldLogfiberLimitMass false = Real.goldenRatio / Real.sqrt 5 ∧
    derivedBinfoldLogfiberLimitMass true = 1 / (Real.goldenRatio * Real.sqrt 5) ∧
    ∀ t : ℝ,
      derivedBinfoldLogfiberLimitMgf t =
        (Real.goldenRatio + Real.goldenRatio ^ (t - 1)) / Real.sqrt 5

private theorem derivedBinfoldLogfiberLimitMgf_closed_form (t : ℝ) :
    derivedBinfoldLogfiberLimitMgf t =
      (Real.goldenRatio + Real.goldenRatio ^ (t - 1)) / Real.sqrt 5 := by
  have hphi0 : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hsqrt5 : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  have hphi : 0 < (Real.goldenRatio : ℝ) := Real.goldenRatio_pos
  unfold derivedBinfoldLogfiberLimitMgf derivedBinfoldLogfiberLimitMass
  have hpow :
      Real.goldenRatio ^ (t - 1) = Real.goldenRatio ^ t / Real.goldenRatio := by
    rw [Real.rpow_sub hphi, Real.rpow_one]
  have hmul :
      (1 / (Real.goldenRatio * Real.sqrt 5)) * Real.goldenRatio ^ t =
        (Real.goldenRatio ^ t / Real.goldenRatio) / Real.sqrt 5 := by
    field_simp [hphi0, hsqrt5]
  calc
    foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true * Real.goldenRatio ^ t =
        Real.goldenRatio / Real.sqrt 5 +
          (1 / (Real.goldenRatio * Real.sqrt 5)) * Real.goldenRatio ^ t := by
            rfl
    _ = Real.goldenRatio / Real.sqrt 5 + (Real.goldenRatio ^ (t - 1)) / Real.sqrt 5 := by
          rw [hmul, ← hpow]
    _ = (Real.goldenRatio + Real.goldenRatio ^ (t - 1)) / Real.sqrt 5 := by
          rw [add_div]

/-- Paper label: `thm:derived-binfold-logfiber-two-point-law`. -/
theorem paper_derived_binfold_logfiber_two_point_law (D : FoldBinTwoStateAsymptoticData) :
    derivedBinfoldLogfiberTwoPointLaw D := by
  refine ⟨paper_fold_bin_two_point_limit_law D, rfl, rfl, rfl, rfl, ?_⟩
  intro t
  exact derivedBinfoldLogfiberLimitMgf_closed_form t

end Omega.Folding
