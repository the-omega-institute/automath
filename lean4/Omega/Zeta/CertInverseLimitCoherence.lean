import Omega.CircleDimension.CertificateInverseLimitAddressing

namespace Omega.Zeta

/-- Paper-facing certificate coherence theorem for the ξ setting: nested closed certificate
intervals with shrinking diameters determine a unique point, and all certificates valid for that
point collapse to a single equivalence class. This is exactly the existing CircleDimension
inverse-limit addressing package, specialized to the ξ certificate vocabulary.
    thm:xi-cert-inverse-limit-coherence -/
theorem paper_xi_cert_inverse_limit_coherence {Cert : Type*} (pointsTo : Cert → ℝ → Prop)
    (equiv : Cert → Cert → Prop) (left right : Cert → ℝ) (chain : ℕ → Cert)
    (hnested :
      ∀ n,
        Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) ⊆
          Set.Icc (left (chain n)) (right (chain n)))
    (hdiam :
      ∀ ε > 0, ∃ N, ∀ n ≥ N, right (chain n) - left (chain n) < ε)
    (hclosed : ∀ n, left (chain n) ≤ right (chain n))
    (hmerge : ∀ C C' θ, pointsTo C θ → pointsTo C' θ → equiv C C') :
    ∃! θ : ℝ, (∀ n, θ ∈ Set.Icc (left (chain n)) (right (chain n))) ∧
      ∀ C C', pointsTo C θ → pointsTo C' θ → equiv C C' := by
  exact Omega.CircleDimension.paper_cdim_certificate_inverse_limit_addressing
    pointsTo equiv left right chain hnested hdiam hclosed hmerge

end Omega.Zeta
