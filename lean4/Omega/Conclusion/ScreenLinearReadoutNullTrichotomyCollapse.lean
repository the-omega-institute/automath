import Omega.SPG.ScreenKernelConnectedComponents
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Trichotomy states for the linear screen readout model. -/
inductive conclusion_screen_linear_readout_null_trichotomy_collapse_status
  | Tot
  | ProtNULL
  | CollNULL
  deriving DecidableEq, Repr

/-- Readout rule: non-image points are protocol-null; image points are total exactly when the
fiber is a singleton, and collision-null otherwise. -/
def conclusion_screen_linear_readout_null_trichotomy_collapse_readout
    (inImage : Bool) (fiberCard : Nat) :
    conclusion_screen_linear_readout_null_trichotomy_collapse_status :=
  if inImage then
    if fiberCard = 1 then
      conclusion_screen_linear_readout_null_trichotomy_collapse_status.Tot
    else
      conclusion_screen_linear_readout_null_trichotomy_collapse_status.CollNULL
  else
    conclusion_screen_linear_readout_null_trichotomy_collapse_status.ProtNULL

/-- Paper-facing collapse statement: outside the image the readout is protocol-null, while on an
affine fiber of cardinality `2^beta` it is total exactly in the zero-kernel case and collision-null
exactly when the kernel rank is positive. -/
def conclusion_screen_linear_readout_null_trichotomy_collapse_statement
    (_m _n : Nat) : Prop :=
  ∀ beta : Nat,
    let fiberCard := 2 ^ beta
    (conclusion_screen_linear_readout_null_trichotomy_collapse_readout false fiberCard =
        conclusion_screen_linear_readout_null_trichotomy_collapse_status.ProtNULL) ∧
      (conclusion_screen_linear_readout_null_trichotomy_collapse_readout true fiberCard =
          conclusion_screen_linear_readout_null_trichotomy_collapse_status.CollNULL ↔
        0 < beta) ∧
      (conclusion_screen_linear_readout_null_trichotomy_collapse_readout true fiberCard =
          conclusion_screen_linear_readout_null_trichotomy_collapse_status.Tot ↔
        beta = 0) ∧
      fiberCard = 2 ^ beta

/-- Paper label: `thm:conclusion-screen-linear-readout-null-trichotomy-collapse`. -/
theorem paper_conclusion_screen_linear_readout_null_trichotomy_collapse
    (m n : Nat) : conclusion_screen_linear_readout_null_trichotomy_collapse_statement m n := by
  intro beta
  dsimp
  have hone :
      2 ^ beta = 1 ↔ beta = 0 := by
    simpa using
      (Omega.SPG.ScreenKernelConnectedComponents.fiber_card_binary (beta + 1)
        (Nat.succ_le_succ (Nat.zero_le beta)))
  refine ⟨by simp [conclusion_screen_linear_readout_null_trichotomy_collapse_readout], ?_, ?_,
    rfl⟩
  · constructor
    · intro hColl
      by_contra hbeta
      have hbeta0 : beta = 0 := Nat.eq_zero_of_not_pos hbeta
      simp [conclusion_screen_linear_readout_null_trichotomy_collapse_readout, hbeta0] at hColl
    · intro hbeta
      have hbeta_ne : beta ≠ 0 := Nat.ne_of_gt hbeta
      have hneq : 2 ^ beta ≠ 1 := by
        intro hsingle
        exact hbeta_ne (hone.mp hsingle)
      unfold conclusion_screen_linear_readout_null_trichotomy_collapse_readout
      rw [if_pos rfl, if_neg hneq]
  · constructor
    · intro hTot
      by_contra hbeta
      have hneq : 2 ^ beta ≠ 1 := by
        intro hsingle
        exact hbeta (hone.mp hsingle)
      have hbeta0 : beta = 0 := by
        simpa [conclusion_screen_linear_readout_null_trichotomy_collapse_readout, hneq] using hTot
      exact hbeta hbeta0
    · intro hbeta
      have hsingle : 2 ^ beta = 1 := hone.mpr hbeta
      simp [conclusion_screen_linear_readout_null_trichotomy_collapse_readout, hsingle]

end Omega.Conclusion
