import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the explicit Kernel-RH bound on the Abel/Mertens finite-part
constant `log M`. The data record the Möbius--Abel expansion, the separate Perron and non-Perron
estimates, the summation of the resulting geometric tails, and the final explicit bound. -/
structure FinitePartLogMKernelRhExplicitBoundData where
  mobiusAbelExpansion : Prop
  perronTermBound : Prop
  nonPerronEigenvalueBound : Prop
  geometricTailSummation : Prop
  explicitBound : Prop
  mobiusAbelExpansion_h : mobiusAbelExpansion
  derivePerronTermBound :
    mobiusAbelExpansion → perronTermBound
  deriveNonPerronEigenvalueBound :
    mobiusAbelExpansion → nonPerronEigenvalueBound
  deriveGeometricTailSummation :
    perronTermBound → nonPerronEigenvalueBound → geometricTailSummation
  deriveExplicitBound :
    mobiusAbelExpansion → perronTermBound → nonPerronEigenvalueBound →
      geometricTailSummation → explicitBound

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the explicit Kernel-RH estimate on the finite-part constant `log M`:
the Möbius--Abel expansion is bounded by separating the Perron contribution from the non-Perron
eigenvalue terms and then summing the resulting geometric tails.
    prop:finite-part-logM-kernel-rh-explicit-bound -/
theorem paper_finite_part_logM_kernel_rh_explicit_bound
    (D : FinitePartLogMKernelRhExplicitBoundData) :
    D.mobiusAbelExpansion ∧
      D.perronTermBound ∧
      D.nonPerronEigenvalueBound ∧
      D.geometricTailSummation ∧
      D.explicitBound := by
  have hPerron : D.perronTermBound := D.derivePerronTermBound D.mobiusAbelExpansion_h
  have hNonPerron : D.nonPerronEigenvalueBound :=
    D.deriveNonPerronEigenvalueBound D.mobiusAbelExpansion_h
  have hTail : D.geometricTailSummation :=
    D.deriveGeometricTailSummation hPerron hNonPerron
  exact ⟨D.mobiusAbelExpansion_h, hPerron, hNonPerron, hTail,
    D.deriveExplicitBound D.mobiusAbelExpansion_h hPerron hNonPerron hTail⟩

end Omega.Zeta
