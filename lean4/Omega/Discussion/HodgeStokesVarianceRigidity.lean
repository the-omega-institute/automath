import Mathlib.Tactic

namespace Omega.Discussion

/-- Chapter-local package for the finite-dimensional Hodge--Stokes variance-rigidity wrapper.
The fields record the `L²` gradient/coclosed splitting, the telescoping reduction of the exact
part to a boundary term, and the transfer of CLT/LDP data from the coclosed component. -/
structure HodgeStokesVarianceRigidityData where
  finiteDimensionalL2EdgeSpace : Prop
  gradientSubspaceClosed : Prop
  coclosedComplementDefined : Prop
  orthogonalDecomposition : Prop
  telescopingReduction : Prop
  cltVarianceRigid : Prop
  ldpRateRigid : Prop
  finiteDimensionalL2EdgeSpace_h : finiteDimensionalL2EdgeSpace
  gradientSubspaceClosed_h : gradientSubspaceClosed
  coclosedComplementDefined_h : coclosedComplementDefined
  deriveOrthogonalDecomposition :
    finiteDimensionalL2EdgeSpace →
      gradientSubspaceClosed →
        coclosedComplementDefined →
          orthogonalDecomposition
  deriveTelescopingReduction :
    orthogonalDecomposition → telescopingReduction
  deriveCltVarianceRigid :
    telescopingReduction → cltVarianceRigid
  deriveLdpRateRigid :
    telescopingReduction → ldpRateRigid

/-- Paper-facing wrapper for the finite-state Hodge--Stokes decomposition: once the
finite-dimensional `L²` edge space splits orthogonally into exact and coclosed parts, the exact
summand telescopes to a boundary term, so the CLT variance and endpoint-speed LDP data depend
only on the coclosed summand.
    thm:discussion-hodge-stokes-variance-rigidity -/
theorem paper_discussion_hodge_stokes_variance_rigidity
    (D : HodgeStokesVarianceRigidityData) :
    D.orthogonalDecomposition ∧
      D.telescopingReduction ∧
      D.cltVarianceRigid ∧
      D.ldpRateRigid := by
  have hOrth : D.orthogonalDecomposition :=
    D.deriveOrthogonalDecomposition
      D.finiteDimensionalL2EdgeSpace_h
      D.gradientSubspaceClosed_h
      D.coclosedComplementDefined_h
  have hTel : D.telescopingReduction :=
    D.deriveTelescopingReduction hOrth
  exact ⟨hOrth, hTel, D.deriveCltVarianceRigid hTel, D.deriveLdpRateRigid hTel⟩

end Omega.Discussion
