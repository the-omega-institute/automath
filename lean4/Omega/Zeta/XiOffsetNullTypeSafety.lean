import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.PhaseNull
import Omega.TypedAddressBiaxialCompletion.UnitarySliceAddressClosure

namespace Omega.Zeta

/-- The explicit modulus of the `L`-offset unitary factor at `s`. -/
noncomputable def xiOffsetUnitaryModulus (L : ℝ) (s : ℂ) : ℝ :=
  L ^ (2 * s.re - 1)

/-- The unitary-slice condition: the modulus is exactly `1`. -/
def xiOffsetUnitarySlice (L : ℝ) (s : ℂ) : Prop :=
  xiOffsetUnitaryModulus L s = 1

/-- Addressability in the Peter-Weyl closure is modeled by membership in the unitary slice. -/
def xiOffsetPwClosureAddressable (L : ℝ) (s : ℂ) : Prop :=
  xiOffsetUnitarySlice L s

/-- Off-slice points collapse to the `NULL` branch of the PW closure. -/
def xiOffsetPwClosureNull (L : ℝ) (s : ℂ) : Prop :=
  ¬ xiOffsetPwClosureAddressable L s

private def xiOffsetUnitarySliceClosureData (L : ℝ) (s : ℂ) :
    Omega.TypedAddressBiaxialCompletion.UnitarySliceAddressClosureData where
  AddressSpace := Unit
  ReadoutCodomain := Unit
  unitarySliceAddress := fun _ => xiOffsetUnitarySlice L s
  guardedReadout := fun _ _ => ()
  guardedRule := True
  readUSClosed := xiOffsetPwClosureAddressable L s → xiOffsetUnitarySlice L s
  hasGuardedRule := trivial
  guardedReadoutCloses := by
    intro _ hAddressable
    exact hAddressable

private lemma xiOffsetUnitarySlice_iff_modulus_one (L : ℝ) (s : ℂ) :
    xiOffsetUnitarySlice L s ↔ xiOffsetUnitaryModulus L s = 1 := by
  rfl

private lemma xiOffsetUnitaryModulus_ne_one {L : ℝ} {s : ℂ} (hL : 1 < L) (hs : s.re ≠ 1 / 2) :
    xiOffsetUnitaryModulus L s ≠ 1 := by
  have hExpNe : 2 * s.re - 1 ≠ 0 := by
    intro hZero
    have hs' : s.re = 1 / 2 := by
      nlinarith
    exact hs hs'
  intro hMod
  have hPowEq : L ^ (2 * s.re - 1) = L ^ (0 : ℝ) := by
    simpa [xiOffsetUnitaryModulus] using hMod
  have hExpZero : 2 * s.re - 1 = (0 : ℝ) :=
    (Real.strictMono_rpow_of_base_gt_one hL).injective hPowEq
  exact hExpNe hExpZero

/-- The explicit offset formula forces every off-critical point off the unit circle; the
unitary-slice closure then blocks PW addressability, so the point lands in the `NULL` branch.
    thm:xi-offset-null-type-safety -/
theorem paper_xi_offset_null_type_safety {L : ℝ} {s : ℂ}
    (hL : 1 < L) (hs : s.re ≠ 1 / 2) :
    xiOffsetUnitaryModulus L s = L ^ (2 * s.re - 1) ∧
      ¬ xiOffsetUnitarySlice L s ∧
      xiOffsetPwClosureNull L s := by
  have hClosure :
      xiOffsetPwClosureAddressable L s → xiOffsetUnitarySlice L s :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_unitary_slice_address_closure
      (xiOffsetUnitarySliceClosureData L s)
  have hNotSlice : ¬ xiOffsetUnitarySlice L s := by
    rw [xiOffsetUnitarySlice_iff_modulus_one]
    exact xiOffsetUnitaryModulus_ne_one hL hs
  have hPhaseNull :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_phase_null True
      (xiOffsetPwClosureAddressable L s) True True (xiOffsetUnitarySlice L s)
      (xiOffsetPwClosureNull L s) trivial
      (by
        intro h hAddressable
        exact h.2 ⟨hAddressable, trivial, trivial, hClosure hAddressable⟩)
  have hNull : xiOffsetPwClosureNull L s := by
    refine hPhaseNull.2 ?_
    intro hAll
    exact hNotSlice hAll.2.2.2
  exact ⟨rfl, hNotSlice, hNull⟩

end Omega.Zeta
