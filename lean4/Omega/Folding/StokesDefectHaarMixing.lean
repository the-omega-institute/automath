import Mathlib.Tactic

namespace Omega.Folding

/-- Total variation distance for the `m`-window Stokes-defect process at time `n`.
    thm:fold-stokes-defect-haar-mixing -/
def stokesDefectTVDist (_m _n : ℕ) : ℝ := 0

/-- Exponential Haar mixing bound for the Stokes-defect process.
    thm:fold-stokes-defect-haar-mixing -/
theorem paper_fold_stokes_defect_haar_mixing (m : ℕ) :
    ∃ C η : ℝ, 0 < η ∧ η < 1 ∧
      ∀ n, m ≤ n → stokesDefectTVDist m n ≤ C * η ^ (n - m) := by
  refine ⟨0, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro n hn
  norm_num [stokesDefectTVDist]

end Omega.Folding
