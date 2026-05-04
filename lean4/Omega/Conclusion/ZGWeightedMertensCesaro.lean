import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter Asymptotics

namespace Omega.Conclusion

noncomputable section

/-- The logarithmic scale for the `k`th weighted harmonic law. -/
def conclusion_zg_weighted_mertens_cesaro_scale (k : ℕ) (X : ℝ) : ℝ :=
  (Real.log X) ^ (k + 1)

/-- The expected main term in the ZG weighted Mertens--Cesaro law. -/
def conclusion_zg_weighted_mertens_cesaro_main (delta : ℝ) (k : ℕ) (X : ℝ) : ℝ :=
  delta / (k + 1 : ℝ) * conclusion_zg_weighted_mertens_cesaro_scale k X

/-- Concrete asymptotic statement for the ZG weighted Mertens--Cesaro law. -/
def conclusion_zg_weighted_mertens_cesaro_law
    (weightedSum : ℝ → ℝ) (delta : ℝ) (k : ℕ) : Prop :=
  (fun X => weightedSum X - conclusion_zg_weighted_mertens_cesaro_main delta k X)
    =o[atTop] conclusion_zg_weighted_mertens_cesaro_scale k

/-- Paper label: `cor:conclusion-zg-weighted-mertens-cesaro`.

This is the final asymptotic transfer step of Abel summation: once the weighted partial sum has
been split into the explicit main term plus an `o((log X)^{k+1})` remainder, the desired weighted
Mertens--Cesaro law follows by rewriting the difference from the main term. -/
theorem paper_conclusion_zg_weighted_mertens_cesaro
    (weightedSum error : ℝ → ℝ) (delta : ℝ) (k : ℕ)
    (hdecomp :
      ∀ X,
        weightedSum X =
          conclusion_zg_weighted_mertens_cesaro_main delta k X + error X)
    (herror : error =o[atTop] conclusion_zg_weighted_mertens_cesaro_scale k) :
    conclusion_zg_weighted_mertens_cesaro_law weightedSum delta k := by
  unfold conclusion_zg_weighted_mertens_cesaro_law
  have hdiff :
      (fun X => weightedSum X - conclusion_zg_weighted_mertens_cesaro_main delta k X) =
        error := by
    funext X
    rw [hdecomp X]
    ring
  simpa [hdiff] using herror

end

end Omega.Conclusion
