import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:real-input-40-p7-projective-branch-genus-tacnode`.
The certified branch and singularity arithmetic gives total ramification `20` and genus `4`. -/
theorem paper_real_input_40_p7_projective_branch_genus_tacnode
    (finiteBranch infinityRamification tacnodeDelta arithmeticGenus : ℕ)
    (hfinite : finiteBranch = 18) (hinfty : infinityRamification = 2)
    (hdelta : tacnodeDelta = 2) (hga : arithmeticGenus = 6) :
    finiteBranch + infinityRamification = 20 ∧ arithmeticGenus - tacnodeDelta = 4 := by
  subst finiteBranch
  subst infinityRamification
  subst tacnodeDelta
  subst arithmeticGenus
  norm_num

end Omega.SyncKernelRealInput
