import Mathlib.Tactic
import Omega.Zeta.FiniteDefectCompleteReconstruction
import Omega.Zeta.XiToeplitzNegativeInertiaMinimalSampling

namespace Omega.Conclusion

/-- The stable negative certificate records the two chapter-local invariants read from the final
Hankel anti-diagonal entry. -/
noncomputable def conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate
    (κ : ℕ) (u : ℕ → ℝ) : ℕ × ℕ :=
  (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia κ u,
    Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_hankelRank κ u)

/-- Tail agreement from a starting index `N`. -/
def conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_eventualAgreementFrom
    (N : ℕ) (u v : ℕ → ℝ) : Prop :=
  ∀ n, N ≤ n → u n = v n

/-- Paper label: `thm:conclusion-toeplitz-shortest-negative-certificate-tail-rigidity`. The full
length-`2κ - 2` jet determines the negative certificate, a shorter jet misses the final Hankel
anti-diagonal entry in general, agreement from that critical tail index already forces the same
certificate, and the finite-defect reconstruction package supplies stability of the readable
defect index together with strictification invariance. -/
theorem paper_conclusion_toeplitz_shortest_negative_certificate_tail_rigidity (κ : ℕ) :
    (∀ u v : ℕ → ℝ,
      Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_fullPrefixAgreement κ u v →
        conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ u =
          conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ v) ∧
      (∃ u v : ℕ → ℝ,
        Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_shortPrefixAgreement κ u v ∧
          Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockSingular κ u ∧
          Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockNonsingular κ v) ∧
      (∀ u v : ℕ → ℝ,
        conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_eventualAgreementFrom
            (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) u v →
          conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ u =
            conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ v) ∧
      (∀ D : Omega.Zeta.FiniteDefectCompleteReconstructionData κ,
        D.kappaReadable ∧ D.strictificationInvariant) := by
  rcases Omega.Zeta.paper_xi_toeplitz_negative_inertia_minimal_sampling κ with ⟨hFull, hShort⟩
  refine ⟨?_, hShort, ?_, ?_⟩
  · intro u v hPrefix
    rcases hFull u v hPrefix with ⟨hNeg, hRank⟩
    exact Prod.ext hNeg hRank
  · intro u v hTail
    have hLast :
        u (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) =
          v (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) :=
      hTail _ le_rfl
    apply Prod.ext <;> simp
      [conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate,
        Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia,
        Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_hankelRank, hLast]
  · intro D
    rcases Omega.Zeta.paper_xi_finite_defect_complete_reconstruction κ D with
      ⟨hkappa, _, _, hStrict⟩
    exact ⟨hkappa, hStrict⟩

end Omega.Conclusion
