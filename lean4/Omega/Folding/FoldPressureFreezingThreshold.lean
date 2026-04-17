import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

/-- Pure arithmetic freezing-threshold squeeze: once the secondary branch lies strictly below the
ground-state line, the lower and upper bounds force equality at that line.
    thm:fold-pressure-freezing-threshold -/
theorem paper_fold_pressure_freezing_threshold (P : Nat → Real) (alphaStar alphaTwo gStar : Real)
    (a : Nat) (hgap : alphaTwo < alphaStar) (hLower : ∀ n, n * alphaStar + gStar ≤ P n)
    (hUpper : ∀ n, P n ≤ max (n * alphaStar + gStar) (n * alphaTwo + Real.log Real.goldenRatio))
    (ha : (Real.log Real.goldenRatio - gStar) / (alphaStar - alphaTwo) < a) :
    P a = a * alphaStar + gStar := by
  have hden : 0 < alphaStar - alphaTwo := sub_pos.mpr hgap
  have ha' : Real.log Real.goldenRatio - gStar < (a : Real) * (alphaStar - alphaTwo) := by
    exact (div_lt_iff₀ hden).mp ha
  have hbranch_lt : (a : Real) * alphaTwo + Real.log Real.goldenRatio <
      (a : Real) * alphaStar + gStar := by
    nlinarith
  have hupperA : P a ≤ (a : Real) * alphaStar + gStar := by
    have h := hUpper a
    rw [max_eq_left_of_lt hbranch_lt] at h
    simpa using h
  have hlowerA : (a : Real) * alphaStar + gStar ≤ P a := by
    simpa using hLower a
  exact le_antisymm hupperA hlowerA

end Omega.Folding
