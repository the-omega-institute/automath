import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete `B3/C3` dictionary vectors for the window-`6` contradiction. -/
abbrev XiWindow6B3C3Vector := ℤ × ℤ × ℤ

/-- The four words used in the paper proof. -/
inductive XiWindow6B3C3WitnessWord where
  | w100000
  | w010000
  | w001000
  | w101000
deriving DecidableEq, Repr

/-- Relevant `B3` dictionary values. -/
def xiWindow6B3Dict : XiWindow6B3C3WitnessWord → XiWindow6B3C3Vector
  | .w100000 => ((1 : ℤ), 0, 0)
  | .w010000 => (0, (1 : ℤ), 0)
  | .w001000 => (0, 0, (1 : ℤ))
  | .w101000 => ((1 : ℤ), (-1 : ℤ), 0)

/-- Relevant `C3` dictionary values. -/
def xiWindow6C3Dict : XiWindow6B3C3WitnessWord → XiWindow6B3C3Vector
  | .w100000 => ((2 : ℤ), 0, 0)
  | .w010000 => (0, (2 : ℤ), 0)
  | .w001000 => (0, 0, (2 : ℤ))
  | .w101000 => ((1 : ℤ), (-1 : ℤ), 0)

/-- Linear extension from the images of the three weight-`1` basis vectors. -/
def xiWindow6LinearApply (u1 u2 u3 : XiWindow6B3C3Vector) :
    XiWindow6B3C3Vector → XiWindow6B3C3Vector
  | (a, b, c) => a • u1 + b • u2 + c • u3

/-- No single linear map can identify the window-`6` `B3` and `C3` root dictionaries on the four
words used in the paper proof. -/
def Window6B3C3NoGlobalLinearUnifier : Prop :=
  ¬ ∃ u1 u2 u3 : XiWindow6B3C3Vector,
      xiWindow6LinearApply u1 u2 u3 (xiWindow6B3Dict .w100000) = xiWindow6C3Dict .w100000 ∧
      xiWindow6LinearApply u1 u2 u3 (xiWindow6B3Dict .w010000) = xiWindow6C3Dict .w010000 ∧
      xiWindow6LinearApply u1 u2 u3 (xiWindow6B3Dict .w001000) = xiWindow6C3Dict .w001000 ∧
      xiWindow6LinearApply u1 u2 u3 (xiWindow6B3Dict .w101000) = xiWindow6C3Dict .w101000

/-- Paper label: `thm:xi-window6-b3c3-no-global-linear-unifier`. -/
theorem paper_xi_window6_b3c3_no_global_linear_unifier : Window6B3C3NoGlobalLinearUnifier := by
  intro h
  rcases h with ⟨u1, u2, u3, h1, h2, h3, h4⟩
  have hu1 : u1 = ((2 : ℤ), 0, 0) := by
    simpa [xiWindow6LinearApply, xiWindow6B3Dict, xiWindow6C3Dict] using h1
  have hu2 : u2 = (0, (2 : ℤ), 0) := by
    simpa [xiWindow6LinearApply, xiWindow6B3Dict, xiWindow6C3Dict] using h2
  have hu3 : u3 = (0, 0, (2 : ℤ)) := by
    simpa [xiWindow6LinearApply, xiWindow6B3Dict, xiWindow6C3Dict] using h3
  subst hu1 hu2 hu3
  have hcalc :
      xiWindow6LinearApply ((2 : ℤ), 0, 0) (0, (2 : ℤ), 0) (0, 0, (2 : ℤ))
          (xiWindow6B3Dict .w101000) = ((2 : ℤ), (-2 : ℤ), 0) := by
    norm_num [xiWindow6LinearApply, xiWindow6B3Dict]
  have hneq :
      (((2 : ℤ), (-2 : ℤ), (0 : ℤ)) : XiWindow6B3C3Vector) =
        ((1 : ℤ), (-1 : ℤ), (0 : ℤ)) := by
    calc
      ((2 : ℤ), (-2 : ℤ), (0 : ℤ)) =
          xiWindow6LinearApply ((2 : ℤ), 0, 0) (0, (2 : ℤ), 0) (0, 0, (2 : ℤ))
            (xiWindow6B3Dict .w101000) := hcalc.symm
      _ = xiWindow6C3Dict .w101000 := by simpa [xiWindow6B3Dict, xiWindow6C3Dict] using h4
      _ = ((1 : ℤ), (-1 : ℤ), (0 : ℤ)) := rfl
  norm_num at hneq
