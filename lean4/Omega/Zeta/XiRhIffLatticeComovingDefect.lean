import Omega.TypedAddressBiaxialCompletion.JensenCountableCriterion
import Omega.Zeta.XiComovingDefectLatticeCertificateBandExclusion

namespace Omega.Zeta

open Omega.TypedAddressBiaxialCompletion
open JensenCountableCriterionData

/-- Paper label: `thm:xi-rh-iff-lattice-comoving-defect`.
The lattice-comoving certificate is available uniformly, so RH is equivalent to vanishing of the
lattice-sampled Jensen defect along the distinguished cofinal radius sequence. -/
theorem paper_xi_rh_iff_lattice_comoving_defect
    (D : JensenCountableCriterionData) (varrho eps delta0 : ℝ) :
    D.rh ↔
      xiComovingDefectLatticeCertificateBandExclusionStatement varrho eps delta0 ∧
        (∀ n : ℕ, D.defect (D.rhoSeq n) = 0) := by
  constructor
  · intro hRh
    refine ⟨paper_xi_comoving_defect_lattice_certificate_band_exclusion varrho eps delta0, ?_⟩
    exact (Omega.TypedAddressBiaxialCompletion.paper_app_jensen_countable_criterion D).1 hRh
  · rintro ⟨_, hdefect⟩
    exact (Omega.TypedAddressBiaxialCompletion.paper_app_jensen_countable_criterion D).2 hdefect

end Omega.Zeta
