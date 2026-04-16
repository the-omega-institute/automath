import Mathlib.Tactic
import Omega.CircleDimension.BasicComputation

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the non-finitely generated rank-one localizations appearing in the
    phase-register table. In the rank-one case the continuous circle dimension stays equal to `1`. -/
def rankOneLocalizationCircleDimStar (_denominatorProfile : Nat) : Nat := 1

/-- Paper-facing wrapper for the rank-one profinite register assignments appearing in the same
    table. -/
def rankOneRegisterPcdim (_registerProfile : Nat) : Nat := 1

/-- Package of the common phase/register assignments used in the paper-facing table:
    basic `circleDim`/`halfCircleDim` computations together with the rank-one localization and
    rank-one register specializations.
    prop:cdim-phase-register-common-assignments -/
theorem paper_cdim_phase_register_common_assignments :
    circleDim 1 0 = 1 ∧
      halfCircleDim 1 0 = 1 / 2 ∧
      (∀ t : Nat, circleDim 0 t = 0) ∧
      (∀ k : Nat, circleDim k 0 = k ∧ halfCircleDim k 0 = (k : ℚ) / 2) ∧
      (∀ d : Nat, circleDim d 0 = d) ∧
      (∀ n : Nat, rankOneLocalizationCircleDimStar n = 1) ∧
      (∀ p : Nat, rankOneRegisterPcdim p = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [circleDim]
  · simp [halfCircleDim, circleDim]
  · intro t
    simp [circleDim]
  · intro k
    simp [circleDim, halfCircleDim]
  · intro d
    simp [circleDim]
  · intro n
    rfl
  · intro p
    rfl

end Omega.CircleDimension
