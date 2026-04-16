import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.FoldResidualTime

set_option maxHeartbeats 400000 in
/-- Above the freezing threshold `a_c`, the affine `τ` law, the normalized pressure identity, and
    escort concentration package into one paper-facing statement.
    thm:frt-apparent-randomness-freezing-escort -/
theorem paper_frt_apparent_randomness_freezing_escort
    (tau P : Nat → ℝ) (EscortConcentrated : Nat → Prop)
    (gStar alphaStar alphaStar₂ logPhi a_c : ℝ) (hGap : alphaStar₂ < alphaStar)
    (ha_c : a_c = (logPhi - gStar) / (alphaStar - alphaStar₂))
    (hTau : ∀ q : Nat, a_c < q → tau q = gStar + (q : ℝ) * alphaStar)
    (hP : ∀ q : Nat, P q = tau q - (q : ℝ) * Real.log 2)
    (hEscort : ∀ q : Nat, a_c < q → EscortConcentrated q) :
    ∀ q : Nat,
      a_c < q →
        tau q = gStar + (q : ℝ) * alphaStar ∧
          P q = gStar + (q : ℝ) * (alphaStar - Real.log 2) ∧ EscortConcentrated q := by
  let _ := hGap
  let _ := ha_c
  intro q hq
  refine ⟨hTau q hq, ?_, hEscort q hq⟩
  rw [hP q, hTau q hq]
  ring

end Omega.FoldResidualTime
