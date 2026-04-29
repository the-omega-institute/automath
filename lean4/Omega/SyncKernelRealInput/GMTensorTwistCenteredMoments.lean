import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:gm-tensor-twist-centered-moments`.
The finite tensor-twist expansion hypothesis and the uniform nontrivial-character spectral-gap
hypothesis jointly provide both asserted centered-moment bounds at each positive order. -/
theorem paper_gm_tensor_twist_centered_moments
    (centeredTrace tensorTwistBound : ℕ → Prop)
    (hExpansion : ∀ ell, 1 ≤ ell → centeredTrace ell)
    (hGap : ∀ ell, 1 ≤ ell → tensorTwistBound ell) :
    ∀ ell, 1 ≤ ell → centeredTrace ell ∧ tensorTwistBound ell := by
  intro ell hell
  exact ⟨hExpansion ell hell, hGap ell hell⟩

end Omega.SyncKernelRealInput
