import Mathlib.Tactic

namespace Omega.Zeta

/-- A finite Toeplitz negative-inertia detector is active when the recorded finite count is
positive. -/
def xi_mom_amplify_detect_true_resonance_detector
    (finiteToeplitzNegativeInertia : ℕ → ℕ) (q : ℕ) : Prop :=
  0 < finiteToeplitzNegativeInertia q

/-- The true resonance predicate is the nonvanishing of the concrete resonance amplitude. -/
def xi_mom_amplify_detect_true_resonance_true_resonance
    (resonanceAmplitude : ℝ) : Prop :=
  resonanceAmplitude ≠ 0

/-- Concrete paper-facing statement for MOM amplification and finite Toeplitz detection. The
MOM values linearly amplify the resonance amplitude; nonzero amplified anomaly activates a finite
negative-inertia detector; and strict positive truncations, forced in the absence of a true
resonance, rule out every detector. -/
def xi_mom_amplify_detect_true_resonance_statement : Prop :=
  ∀ (resonanceAmplitude : ℝ)
    (momAmplitude strictifiedFiniteTruncation : ℕ → ℝ)
    (finiteToeplitzNegativeInertia : ℕ → ℕ),
    (∀ q : ℕ, momAmplitude q = (q : ℝ) * resonanceAmplitude) →
      (∀ q : ℕ, momAmplitude q ≠ 0 →
        xi_mom_amplify_detect_true_resonance_detector finiteToeplitzNegativeInertia q) →
      (resonanceAmplitude = 0 → ∀ q : ℕ, 0 < strictifiedFiniteTruncation q) →
      (∀ q : ℕ, 0 < strictifiedFiniteTruncation q → finiteToeplitzNegativeInertia q = 0) →
        (xi_mom_amplify_detect_true_resonance_true_resonance resonanceAmplitude ↔
          ∃ q : ℕ, 0 < q ∧
            xi_mom_amplify_detect_true_resonance_detector finiteToeplitzNegativeInertia q)

/-- Paper label: `thm:xi-mom-amplify-detect-true-resonance`. -/
theorem paper_xi_mom_amplify_detect_true_resonance :
    xi_mom_amplify_detect_true_resonance_statement := by
  intro resonanceAmplitude momAmplitude strictifiedFiniteTruncation finiteToeplitzNegativeInertia
    hAmplifies hDetects hStrictPositive hPositiveRulesOut
  constructor
  · intro hTrue
    refine ⟨1, by norm_num, ?_⟩
    apply hDetects
    have hMom : momAmplitude 1 = resonanceAmplitude := by
      simpa using hAmplifies 1
    simpa [hMom] using hTrue
  · rintro ⟨q, _hq, hDetector⟩
    by_contra hTrue
    have hZero : resonanceAmplitude = 0 := not_not.mp hTrue
    have hPositive : 0 < strictifiedFiniteTruncation q := hStrictPositive hZero q
    have hNoDetector : finiteToeplitzNegativeInertia q = 0 := hPositiveRulesOut q hPositive
    rw [xi_mom_amplify_detect_true_resonance_detector, hNoDetector] at hDetector
    exact (Nat.lt_irrefl 0) hDetector

end Omega.Zeta
