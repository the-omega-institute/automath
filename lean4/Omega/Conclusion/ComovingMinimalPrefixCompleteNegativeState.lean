import Mathlib.Data.Complex.Basic
import Omega.Conclusion.ToeplitzStrictificationQuotientNegativeCertificateThreshold
import Omega.Conclusion.ToeplitzNegativeGeometryStrictificationOrthogonalSplit

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-comoving-minimal-prefix-complete-negative-state`. -/
theorem paper_conclusion_comoving_minimal_prefix_complete_negative_state
    {β : Type*} (audit : (ℂ → ℂ) → β) (hAudit : toeplitzAuditFactorsThroughKernel audit)
    (κ : ℕ) (hκ : 1 ≤ κ) :
    (∀ u v : ℕ → ℝ,
      Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_fullPrefixAgreement κ u v →
        conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ u =
          conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ v) ∧
      Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ + 1 = 2 * κ - 1 := by
  rcases paper_conclusion_toeplitz_strictification_quotient_negative_certificate_threshold
      audit hAudit κ hκ with
    ⟨hfull, _, _, _, hlast⟩
  exact ⟨hfull, hlast⟩

end Omega.Conclusion
