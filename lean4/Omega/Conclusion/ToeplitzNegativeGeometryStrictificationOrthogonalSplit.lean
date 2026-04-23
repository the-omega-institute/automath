import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Omega.Conclusion.ToeplitzShortestNegativeCertificateTailRigidity
import Omega.Conclusion.VisibleJointHorizonSharp2d
import Omega.Conclusion.ToeplitzGaugeBlindnessZeroDimensionalLedgerNecessity
import Omega.Zeta.ToeplitzNegativeSpectrumProductDetHankelSquare

namespace Omega.Conclusion

open Matrix
open scoped BigOperators

/-- The diagonal Hankel Gram block that records the negative Toeplitz directions in the simplified
chart used in this wrapper. -/
def toeplitzNegativeGramBlock {κ : ℕ} (σ : Fin κ → ℝ) : Matrix (Fin κ) (Fin κ) ℝ :=
  Matrix.diagonal fun i => (σ i) ^ (2 : ℕ)

/-- The explicit negative witness carried by the block `-H*H`: the quadratic form is the negative
sum of squared coordinates after the singular-value weighting. -/
def toeplitzNegativeWitness {κ : ℕ} (σ v : Fin κ → ℝ) : ℝ :=
  -∑ i, ((σ i) * (v i)) ^ (2 : ℕ)

private lemma toeplitzNegativeWitness_nonpos {κ : ℕ} (σ v : Fin κ → ℝ) :
    toeplitzNegativeWitness σ v ≤ 0 := by
  unfold toeplitzNegativeWitness
  have hsum_nonneg : 0 ≤ ∑ i, ((σ i) * (v i)) ^ (2 : ℕ) := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg ((σ i) * (v i))
  linarith

private lemma toeplitzNegativeWitness_neg {κ : ℕ} (σ v : Fin κ → ℝ)
    (hnonzero : ∃ i, σ i * v i ≠ 0) :
    toeplitzNegativeWitness σ v < 0 := by
  rcases hnonzero with ⟨i, hi⟩
  unfold toeplitzNegativeWitness
  have hterm_pos : 0 < ((σ i) * (v i)) ^ (2 : ℕ) := by
    exact sq_pos_iff.mpr hi
  have hsum_nonneg : 0 ≤ ∑ j, ((σ j) * (v j)) ^ (2 : ℕ) := by
    exact Finset.sum_nonneg fun j _ => sq_nonneg ((σ j) * (v j))
  have hsingle :
      ((σ i) * (v i)) ^ (2 : ℕ) ≤ ∑ j, ((σ j) * (v j)) ^ (2 : ℕ) := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg ((σ j) * (v j))) (by simp)
  have hsum_pos : 0 < ∑ j, ((σ j) * (v j)) ^ (2 : ℕ) := lt_of_lt_of_le hterm_pos hsingle
  linarith

/-- Paper label: `thm:conclusion-toeplitz-negative-geometry-strictification-orthogonal-split`.
The negative Toeplitz block is explicitly represented by a Hankel-Gram diagonal chart, its witness
quadratic form is strictly negative whenever a weighted coordinate survives, and the strictification
shift `C ↦ C + i η` remains invisible to every audit that factors through the Carath--Pick kernel. -/
theorem paper_conclusion_toeplitz_negative_geometry_strictification_orthogonal_split
    {β : Type*} (audit : (ℂ → ℂ) → β)
    (hAudit : toeplitzAuditFactorsThroughKernel audit)
    {κ : ℕ} (σ v : Fin κ → ℝ) (C : ℂ → ℂ) (η : ℝ)
    (hnonzero : ∃ i, σ i * v i ≠ 0) :
    audit (toeplitzGaugeShift C η) = audit C ∧
      (∀ w z,
        Omega.Zeta.carathPickKernel (toeplitzGaugeShift C η) w z =
          Omega.Zeta.carathPickKernel C w z) ∧
      toeplitzNegativeWitness σ v = -∑ i, ((σ i) * (v i)) ^ (2 : ℕ) ∧
      toeplitzNegativeWitness σ v < 0 ∧
      toeplitzNegativeWitness σ v ≤ 0 ∧
      (∏ i, |(-(σ i) ^ (2 : ℕ))|) = Matrix.det (toeplitzNegativeGramBlock σ) := by
  refine ⟨hAudit (carathPickKernel_toeplitzGaugeShift C η),
    carathPickKernel_toeplitzGaugeShift C η, rfl,
    toeplitzNegativeWitness_neg σ v hnonzero,
    toeplitzNegativeWitness_nonpos σ v, ?_⟩
  simpa [toeplitzNegativeGramBlock] using Omega.Zeta.paper_xi_negative_spectrum_product_dethankel_square σ

/-- The two-parameter revelation package at prefix length `L` and depth `N`: the stable negative
certificate is fixed by every moment prefix of length `L + 1`, and the visible reconstruction side
has reached the joint Toeplitz/Prony horizon `N`. -/
def conclusion_toeplitz_defect_revelation_two_parameter_irreducibility_reveals
    (κ L N : ℕ) (D : Omega.Zeta.FiniteDefectCompleteReconstructionData κ) : Prop :=
  (∀ u v : ℕ → ℝ, (∀ n ≤ L, u n = v n) →
    conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ u =
      conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ v) ∧
    visibleJointHorizon κ ≤ N ∧
    D.kappaReadable ∧
    D.reconstructionFrom4KappaSamples ∧
    D.reconstructionFromMomentSegment

/-- Paper label: `thm:conclusion-toeplitz-defect-revelation-two-parameter-irreducibility`. The
certificate-length lower bound `2κ - 2` comes from the shortest negative-certificate witness, the
depth lower bound `2κ` is the sharp visible joint horizon, and at that exact parameter pair the
finite-defect reconstruction and the strict negative Toeplitz witness are both available. -/
theorem paper_conclusion_toeplitz_defect_revelation_two_parameter_irreducibility
    {β : Type*} (audit : (ℂ → ℂ) → β)
    (hAudit : toeplitzAuditFactorsThroughKernel audit)
    (κ : ℕ) (D : Omega.Zeta.FiniteDefectCompleteReconstructionData κ)
    (σ v : Fin κ → ℝ) (C : ℂ → ℂ) (η : ℝ)
    (hnonzero : ∃ i, σ i * v i ≠ 0) (hκ : 1 ≤ κ) :
    (∀ L : ℕ,
      L < Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ →
        ¬ conclusion_toeplitz_defect_revelation_two_parameter_irreducibility_reveals
            κ L (visibleJointHorizon κ) D) ∧
      (∀ N : ℕ,
        N < visibleJointHorizon κ →
          ¬ conclusion_toeplitz_defect_revelation_two_parameter_irreducibility_reveals
              κ (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) N D) ∧
      conclusion_toeplitz_defect_revelation_two_parameter_irreducibility_reveals
          κ (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ)
            (visibleJointHorizon κ) D ∧
      toeplitzNegativeWitness σ v < 0 := by
  rcases paper_conclusion_toeplitz_shortest_negative_certificate_tail_rigidity κ with
    ⟨hFull, hShort, _, _⟩
  rcases Omega.Zeta.paper_xi_finite_defect_complete_reconstruction κ D with
    ⟨hReadable, h4κ, h2κ, _⟩
  rcases paper_conclusion_toeplitz_negative_geometry_strictification_orthogonal_split
      audit hAudit σ v C η hnonzero with
    ⟨_, _, _, hneg, _, _⟩
  refine ⟨?_, ?_, ?_, hneg⟩
  · intro L hL hReveal
    rcases hShort with ⟨u, v, hShortPrefix, hSing, hNon⟩
    have hPrefix : ∀ n ≤ L, u n = v n := by
      intro n hn
      exact hShortPrefix n (lt_of_le_of_lt hn hL)
    have hCertEq :=
      hReveal.1 u v hPrefix
    have hCertNe :
        conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ u ≠
          conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate κ v := by
      have hSing' :
          u (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) = 0 := by
        simpa [Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockSingular] using
          hSing
      have hNon' :
          v (Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) ≠ 0 := by
        simpa [Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockNonsingular] using
          hNon
      intro h
      have hfst := congrArg Prod.fst h
      have hkNe : κ - 1 ≠ κ := by omega
      simp [conclusion_toeplitz_shortest_negative_certificate_tail_rigidity_certificate,
        Omega.Zeta.xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia, hSing', hNon'] at hfst
      exact hkNe hfst
    exact hCertNe hCertEq
  · intro N hN hReveal
    exact (not_le_of_gt hN) hReveal.2.1
  · refine ⟨?_, le_rfl, hReadable, h4κ, h2κ⟩
    intro u v hPrefix
    exact hFull u v hPrefix

end Omega.Conclusion
