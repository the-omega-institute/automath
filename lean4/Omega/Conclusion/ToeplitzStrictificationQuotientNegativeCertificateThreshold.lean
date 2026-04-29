import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.ToeplitzGaugeBlindnessZeroDimensionalLedgerNecessity
import Omega.Conclusion.ToeplitzShortestNegativeCertificateTailRigidity

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper label: `thm:conclusion-toeplitz-strictification-quotient-negative-certificate-threshold`.
The stable Toeplitz negative certificate is exactly controlled by the prefix ending at
`2κ - 2`; any shorter prefix admits a singular/nonsingular ambiguity witness, while every
strictification-gauge-invariant audit remains blind to the extra `η`-parameter. -/
theorem paper_conclusion_toeplitz_strictification_quotient_negative_certificate_threshold
    {β : Type*} (audit : (ℂ → ℂ) → β) (hAudit : toeplitzAuditFactorsThroughKernel audit)
    (κ : ℕ) (hκ : 1 ≤ κ) :
    (∀ u v : ℕ → ℝ,
      xi_toeplitz_negative_inertia_minimal_sampling_fullPrefixAgreement κ u v →
        conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ u =
          conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ v) ∧
      (∀ L : ℕ,
        L < xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ →
          ∃ u v : ℕ → ℝ,
            (∀ n ≤ L, u n = v n) ∧
              conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ u ≠
                conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ v) ∧
      (∀ C η, audit (toeplitzGaugeShift C η) = audit C) ∧
      xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ = 2 * κ - 2 ∧
      xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ + 1 = 2 * κ - 1 := by
  rcases paper_conclusion_toeplitz_shortest_negative_certificate_tail_rigidity κ with
    ⟨hfull, hshort, _, _⟩
  refine ⟨hfull, ?_, ?_, rfl, ?_⟩
  · intro L hL
    rcases hshort with ⟨u, v, hprefix, hsing, hnon⟩
    refine ⟨u, v, ?_, ?_⟩
    · intro n hn
      exact hprefix n (lt_of_le_of_lt hn hL)
    · intro hcert
      have hfst := congrArg Prod.fst hcert
      have hkappa_ne : κ - 1 ≠ κ := by
        omega
      have hsing' :
          u (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) = 0 := by
        simpa [xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockSingular] using hsing
      have hnon' :
          v (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) ≠ 0 := by
        simpa [xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockNonsingular] using hnon
      simp [conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate,
        xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia, hsing', hnon'] at hfst
      exact hkappa_ne hfst
  · intro C η
    exact hAudit (carathPickKernel_toeplitzGaugeShift C η)
  · change (2 * κ - 2) + 1 = 2 * κ - 1
    omega

end Omega.Conclusion
