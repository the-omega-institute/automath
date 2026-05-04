import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-leyang-crossratio-projective-fingerprint-complete`.
This is the paper-facing invariant-completeness wrapper: the supplied completeness hypothesis
turns equality of finite cross-ratio fingerprints into projective equivalence. -/
theorem paper_xi_leyang_crossratio_projective_fingerprint_complete {Config Fingerprint : Type}
    (fingerprint : Config -> Fingerprint)
    (projectivelyEquivalent : Config -> Config -> Prop)
    (hcomplete :
      forall A B : Config, fingerprint A = fingerprint B -> projectivelyEquivalent A B) :
    forall A B : Config, fingerprint A = fingerprint B -> projectivelyEquivalent A B := by
  exact hcomplete

end Omega.Zeta
