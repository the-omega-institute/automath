import Mathlib.Tactic
import Omega.Conclusion.OddtailFiniteDepthScalarPadeJacobiRigidity

namespace Omega.Conclusion

/-- Paper-facing contradiction wrapper for `thm:conclusion-oddtail-no-scalar-unifying-pi-kernel`.
Any scalar kernel would force the three incompatible odd-tail shadows simultaneously, so it
cannot exist. -/
theorem paper_conclusion_oddtail_no_scalar_unifying_pi_kernel
    (scalarKernel finiteRegularity nonDFiniteShadow nonFiniteGapHost : Prop)
    (hRegularity : scalarKernel -> finiteRegularity)
    (hShadow : scalarKernel -> nonDFiniteShadow)
    (hHost : scalarKernel -> nonFiniteGapHost)
    (hContradiction : finiteRegularity -> nonDFiniteShadow -> nonFiniteGapHost -> False) :
    Not scalarKernel := by
  intro hKernel
  exact hContradiction (hRegularity hKernel) (hShadow hKernel) (hHost hKernel)

end Omega.Conclusion
