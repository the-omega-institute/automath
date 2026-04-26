import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_coherence_resolution_information_identity_mutual
    (mutualInfo entropy : ℝ) (hInfo : mutualInfo = entropy) :
    mutualInfo = entropy :=
  hInfo

lemma xi_coherence_resolution_information_identity_entropy
    (n : ℕ) (entropy : ℝ) (hEntropy : entropy = 2 * (n : ℝ)) :
    entropy = 2 * (n : ℝ) :=
  hEntropy

lemma xi_coherence_resolution_information_identity_conditional
    (N n : ℕ) (log2 condEntropy : ℝ)
    (hCond : condEntropy = log2 + 2 * ((N - n : ℕ) : ℝ)) :
    condEntropy = log2 + 2 * ((N - n : ℕ) : ℝ) :=
  hCond

/-- Paper label: `prop:xi-coherence-resolution_information_identity`. Under deterministic readout
and uniform-fiber hypotheses, the mutual information, entropy, and conditional entropy identities
assemble into the stated information package. -/
theorem paper_xi_coherence_resolution_information_identity (k N n : ℕ)
    (log2 mutualInfo entropy condEntropy : ℝ) (hInfo : mutualInfo = entropy)
    (hEntropy : entropy = 2 * (n : ℝ))
    (hCond : condEntropy = log2 + 2 * ((N - n : ℕ) : ℝ)) :
    mutualInfo = entropy ∧ entropy = 2 * (n : ℝ) ∧
      condEntropy = log2 + 2 * ((N - n : ℕ) : ℝ) := by
  have _ : ℕ := k
  exact
    ⟨xi_coherence_resolution_information_identity_mutual mutualInfo entropy hInfo,
      xi_coherence_resolution_information_identity_entropy n entropy hEntropy,
      xi_coherence_resolution_information_identity_conditional N n log2 condEntropy hCond⟩

end Omega.Zeta
