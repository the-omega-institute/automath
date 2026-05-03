import Omega.Zeta.XiWindow6ResetGapMgfMoments

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-reset-gap-fib-coupling`. -/
theorem paper_xi_window6_reset_gap_fib_coupling (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (hprob : 1 / phi + 1 / phi ^ 2 = 1) :
    let mean : ℝ := 55 / phi + 34 / phi ^ 2
    mean = 13 + 21 * phi ∧
      (55 - mean) ^ 2 / phi + (34 - mean) ^ 2 / phi ^ 2 =
        21 ^ 2 * (2 * phi - 3) := by
  rcases paper_xi_window6_reset_gap_mgf_moments phi hphi hprob with ⟨hmean, hvar⟩
  refine ⟨hmean, ?_⟩
  have h441 : (441 : ℝ) = 21 ^ 2 := by norm_num
  simpa [h441] using hvar

end Omega.Zeta
