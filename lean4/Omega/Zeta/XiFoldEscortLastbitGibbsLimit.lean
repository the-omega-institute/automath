import Omega.Zeta.XiFoldbinEscortTvCollapseOnebitGibbs

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-escort-lastbit-gibbs-limit`.
The closed Gibbs parameter formula, with the original push-forward case `q = 1`. -/
theorem paper_xi_fold_escort_lastbit_gibbs_limit :
    (∀ q : ℝ,
      xi_foldbin_escort_tv_collapse_onebit_gibbs_gibbs_theta q =
        1 / (1 + Real.goldenRatio ^ (q + 1))) ∧
      xi_foldbin_escort_tv_collapse_onebit_gibbs_gibbs_theta 1 =
        1 / (1 + Real.goldenRatio ^ (2 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro q
    rfl
  · unfold xi_foldbin_escort_tv_collapse_onebit_gibbs_gibbs_theta
    congr 2
    norm_num

end Omega.Zeta
