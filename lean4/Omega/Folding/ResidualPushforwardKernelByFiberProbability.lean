import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.FiberConditionalReconstructionOddModulus
import Omega.Folding.FiberSingleCoordinateAffineDifference

namespace Omega.Folding

/-- The fiberwise conditional probability that the selected bit equals `1`. -/
def foldResidualFiberProbability (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) : ℚ :=
  (foldFiberSingleCoordinateOneCount m k r : ℚ) / (foldFiberSingleCoordinateProfile m k r : ℚ)

/-- The one-step pushforward kernel induced by choosing coordinate `k` with probability `1 / m`
and then conditioning on the residue fiber. -/
def foldResidualPushforwardKernel (m k : ℕ)
    (r s : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) : ℚ :=
  if s = r + foldFiberSingleCoordinateAffineDifferenceShift m k then
    ((foldFiberSingleCoordinateProfile m k r - foldFiberSingleCoordinateOneCount m k r : ℕ) : ℚ) /
      ((m : ℚ) * (foldFiberSingleCoordinateProfile m k r : ℚ))
  else if s = r - foldFiberSingleCoordinateAffineDifferenceShift m k then
    (foldFiberSingleCoordinateOneCount m k r : ℚ) /
      ((m : ℚ) * (foldFiberSingleCoordinateProfile m k r : ℚ))
  else
    0

private noncomputable def foldResidualProfileEquivBool (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    {x : foldFiberSingleCoordinateState m // foldFiberSingleCoordinateResidue m k x = r} ≃ Bool where
  toFun x := x.1.2
  invFun b := ⟨(r - if b then foldFiberSingleCoordinateAffineDifferenceShift m k else 0, b), by
    simp [foldFiberSingleCoordinateResidue]⟩
  left_inv x := by
    rcases x with ⟨⟨s, b⟩, hx⟩
    have hs : s = r - if b then foldFiberSingleCoordinateAffineDifferenceShift m k else 0 := by
      simpa [foldFiberSingleCoordinateResidue] using eq_sub_of_add_eq hx
    apply Subtype.ext
    simp [hs]
  right_inv b := by
    simp

private theorem foldResidualProfile_eq_two (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldFiberSingleCoordinateProfile m k r = 2 := by
  classical
  unfold foldFiberSingleCoordinateProfile
  simpa using Fintype.card_congr (foldResidualProfileEquivBool m k r)

private noncomputable def foldResidualOneCountEquivFinOne (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    {x : foldFiberSingleCoordinateState m //
      x.2 = true ∧ foldFiberSingleCoordinateResidue m k x = r} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨(r - foldFiberSingleCoordinateAffineDifferenceShift m k, true), by
    simp [foldFiberSingleCoordinateResidue]⟩
  left_inv x := by
    rcases x with ⟨⟨s, b⟩, hx⟩
    rcases hx with ⟨hb, hr⟩
    have hb' : b = true := by simpa using hb
    subst b
    have hs : s = r - foldFiberSingleCoordinateAffineDifferenceShift m k := by
      simpa [foldFiberSingleCoordinateResidue] using eq_sub_of_add_eq hr
    apply Subtype.ext
    simp [hs]
  right_inv i := by
    fin_cases i
    rfl

private theorem foldResidualOneCount_eq_one (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldFiberSingleCoordinateOneCount m k r = 1 := by
  classical
  unfold foldFiberSingleCoordinateOneCount
  simpa using Fintype.card_congr (foldResidualOneCountEquivFinOne m k r)

/-- Paper label: `prop:fold-residual-pushforward-kernel-by-fiber-probability`.
Conditioning on the flipped bit turns the `+F_{k+1}` branch into the bit-`0` fraction of the
fiber and the `-F_{k+1}` branch into the bit-`1` fraction. -/
theorem paper_fold_residual_pushforward_kernel_by_fiber_probability (m k : ℕ) :
    ∀ r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m),
      foldResidualPushforwardKernel m k r (r + foldFiberSingleCoordinateAffineDifferenceShift m k) =
          (1 / (m : ℚ)) * (1 - foldResidualFiberProbability m k r) ∧
        foldResidualPushforwardKernel m k r (r - foldFiberSingleCoordinateAffineDifferenceShift m k) =
          (1 / (m : ℚ)) * foldResidualFiberProbability m k r := by
  intro r
  have hProfileNat : foldFiberSingleCoordinateProfile m k r = 2 :=
    foldResidualProfile_eq_two m k r
  have hOneNat : foldFiberSingleCoordinateOneCount m k r = 1 :=
    foldResidualOneCount_eq_one m k r
  have hProfile : (foldFiberSingleCoordinateProfile m k r : ℚ) = 2 := by
    norm_num [hProfileNat]
  have hOne : (foldFiberSingleCoordinateOneCount m k r : ℚ) = 1 := by
    norm_num [hOneNat]
  have hDiff : ((foldFiberSingleCoordinateProfile m k r -
      foldFiberSingleCoordinateOneCount m k r : ℕ) : ℚ) = 1 := by
    norm_num [hProfileNat, hOneNat]
  by_cases hm0 : m = 0
  · subst hm0
    simp [foldResidualPushforwardKernel, foldResidualFiberProbability, hProfile, hOne, hDiff]
  · have hmq : (m : ℚ) ≠ 0 := by
      exact_mod_cast hm0
    constructor
    · simp [foldResidualPushforwardKernel, foldResidualFiberProbability, hProfile, hOne]
      rw [hDiff]
      field_simp [hmq]
      ring
    · by_cases hsame :
          r - foldFiberSingleCoordinateAffineDifferenceShift m k =
            r + foldFiberSingleCoordinateAffineDifferenceShift m k
      · simp [foldResidualPushforwardKernel, foldResidualFiberProbability, hProfile, hOne, hDiff,
          hsame]
        field_simp [hmq]
      · simp [foldResidualPushforwardKernel, foldResidualFiberProbability, hProfile, hOne,
          hsame]
        field_simp [hmq]

end Omega.Folding
