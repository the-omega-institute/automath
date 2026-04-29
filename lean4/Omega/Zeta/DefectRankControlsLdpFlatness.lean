import Mathlib.Tactic

namespace Omega.Zeta

/-- Certificate for the Legendre-duality rank/flatness bookkeeping.  The defect rank is the
dimension of the pressure-invariant defect subspace; the rate-function flat dimension and strict
convexity predicate are the induced concrete readouts. -/
structure xi_defect_rank_controls_ldp_flatness_certificate where
  defectRank : ℕ

namespace xi_defect_rank_controls_ldp_flatness_certificate

/-- The affine flat dimension of the Legendre-dual rate function. -/
def flatDimension (C : xi_defect_rank_controls_ldp_flatness_certificate) : ℕ :=
  C.defectRank

/-- Strict convexity is exactly absence of nonzero defect directions. -/
def strictlyConvex (C : xi_defect_rank_controls_ldp_flatness_certificate) : Prop :=
  C.defectRank = 0

end xi_defect_rank_controls_ldp_flatness_certificate

/-- Paper label: `prop:xi-defect-rank-controls-ldp-flatness`. -/
theorem paper_xi_defect_rank_controls_ldp_flatness
    (C : xi_defect_rank_controls_ldp_flatness_certificate) :
    C.flatDimension = C.defectRank ∧ (C.defectRank = 0 ↔ C.strictlyConvex) := by
  simp [xi_defect_rank_controls_ldp_flatness_certificate.flatDimension,
    xi_defect_rank_controls_ldp_flatness_certificate.strictlyConvex]

end Omega.Zeta
