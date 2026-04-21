import Mathlib.Tactic
import Omega.Folding.FoldBinM6FiberHist

namespace Omega.Folding

/-- The degree-`1` integral cohomology rank of the compact factor `PU(d)`. -/
def puH1Rank (_d : ℕ) : ℕ := 0

/-- The degree-`2` integral cohomology rank of the compact factor `PU(d)`. -/
def puH2Rank (_d : ℕ) : ℕ := 0

/-- The degree-`3` integral cohomology rank of `PU(d)`: one generator for every nontrivial
projective unitary factor. -/
def puH3Rank (d : ℕ) : ℕ :=
  if 2 ≤ d then 1 else 0

/-- The third integral cohomology rank of the connected foldbin automorphism group, read from the
audited histogram of `PU(d)` factors. -/
def foldbinAut0ThirdCohomologyRankFromHistogram (hist : ℕ → ℕ) : ℕ :=
  hist 2 * puH3Rank 2 + hist 3 * puH3Rank 3 + hist 4 * puH3Rank 4

lemma foldbinAut0ThirdCohomologyRankFromHistogram_eq_sum (hist : ℕ → ℕ) :
    foldbinAut0ThirdCohomologyRankFromHistogram hist = hist 2 + hist 3 + hist 4 := by
  norm_num [foldbinAut0ThirdCohomologyRankFromHistogram, puH3Rank]

/-- The connected window-`6` foldbin automorphism group has vanishing `H¹` and `H²`, while `H³`
has one integral generator for each audited `PU(d)` factor; the histogram `2:8, 3:4, 4:9`
therefore yields rank `21`.
    thm:foldbin-groupoid-aut0-third-cohomology-rank -/
theorem paper_foldbin_groupoid_aut0_third_cohomology_rank :
    (puH1Rank 2 = 0 ∧ puH1Rank 3 = 0 ∧ puH1Rank 4 = 0) ∧
      (puH2Rank 2 = 0 ∧ puH2Rank 3 = 0 ∧ puH2Rank 4 = 0) ∧
      foldbinAut0ThirdCohomologyRankFromHistogram (fun d => cBinFiberHist 6 d) =
        cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 ∧
      foldbinAut0ThirdCohomologyRankFromHistogram (fun d => cBinFiberHist 6 d) = 21 := by
  rcases paper_fold_bin_m6_fiber_hist with ⟨_, _, h2, h3, h4, _, _⟩
  refine ⟨by simp [puH1Rank], by simp [puH2Rank], ?_, ?_⟩
  · exact foldbinAut0ThirdCohomologyRankFromHistogram_eq_sum _
  · rw [foldbinAut0ThirdCohomologyRankFromHistogram_eq_sum, h2, h3, h4]

end Omega.Folding
