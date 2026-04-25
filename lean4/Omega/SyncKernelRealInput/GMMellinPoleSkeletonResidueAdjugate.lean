import Omega.SyncKernelRealInput.GMMellinMeromorphicFingerprint

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-mellin-pole-skeleton-residue-adjugate`.  The
determinant/adjugate Mellin fingerprint transports first to the pole skeleton and then to
the residue formula. -/
theorem paper_gm_mellin_pole_skeleton_residue_adjugate
    (D : Omega.SyncKernelRealInput.gm_mellin_meromorphic_fingerprint_data)
    (poleSkeleton residueFormula : Prop) (hskeleton : D.statement → poleSkeleton)
    (hresidue : poleSkeleton → residueFormula) :
    D.statement → poleSkeleton ∧ residueFormula := by
  intro hD
  exact ⟨hskeleton hD, hresidue (hskeleton hD)⟩

end Omega.SyncKernelRealInput
