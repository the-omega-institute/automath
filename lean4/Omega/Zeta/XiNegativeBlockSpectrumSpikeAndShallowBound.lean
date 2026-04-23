import Mathlib.Tactic
import Omega.Zeta.XiHankelSpikeSingularSpectrumSeparation

namespace Omega.Zeta

/-- Concrete Gram/negative-block package attached to the rank-one Hankel spike model. The Gram
eigenvalues are identified with squared singular values, the negative block is `-G`, and the spike
gap `|u₀| - κ B` is assumed nonnegative so that the leading lower bound can be squared. -/
structure XiNegativeBlockSpectrumSpikeAndShallowBoundData where
  spikeData : XiHankelSpikeSingularSpectrumData
  gramEigenvalue : ℕ → ℝ
  negativeBlockEigenvalue : ℕ → ℝ
  xi_negative_block_spectrum_spike_and_shallow_bound_singular_nonneg :
    ∀ j : ℕ, 0 ≤ spikeData.singularValue j
  xi_negative_block_spectrum_spike_and_shallow_bound_gram_sq :
    ∀ j : ℕ, gramEigenvalue j = spikeData.singularValue j ^ 2
  xi_negative_block_spectrum_spike_and_shallow_bound_negative_eq :
    ∀ j : ℕ, negativeBlockEigenvalue j = -gramEigenvalue j
  xi_negative_block_spectrum_spike_and_shallow_bound_gap_nonneg :
    0 ≤ |spikeData.u0| - (spikeData.κ : ℝ) * spikeData.B

/-- Paper-facing Gram and shallow-negative spectral bounds for the Hankel spike package. -/
def xi_negative_block_spectrum_spike_and_shallow_bound_statement
    (D : XiNegativeBlockSpectrumSpikeAndShallowBoundData) : Prop :=
  (|D.spikeData.u0| - (D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2 ≤ D.gramEigenvalue 1 ∧
    (∀ j : ℕ, 2 ≤ j → D.gramEigenvalue j ≤ ((D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2) ∧
    D.negativeBlockEigenvalue 1 ≤
      -(|D.spikeData.u0| - (D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2 ∧
    (∀ j : ℕ, 2 ≤ j → -((D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2 ≤ D.negativeBlockEigenvalue j)

/-- Paper label: `cor:xi-negative-block-spectrum-spike-and-shallow-bound`. The previous
singular-spectrum separation theorem supplies the leading/tail singular-value bounds, and the
present wrapper squares them to obtain the corresponding Gram eigenvalue estimates and the
shallow-negative bounds for `-G`. -/
theorem paper_xi_negative_block_spectrum_spike_and_shallow_bound
    (D : XiNegativeBlockSpectrumSpikeAndShallowBoundData) :
    xi_negative_block_spectrum_spike_and_shallow_bound_statement D := by
  rcases paper_xi_hankel_spike_singular_spectrum_separation D.spikeData with ⟨hLead, hTail⟩
  have hκB_nonneg : 0 ≤ (D.spikeData.κ : ℝ) * D.spikeData.B := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le D.spikeData.κ) D.spikeData.hB_nonneg
  have hLead_sq :
      (|D.spikeData.u0| - (D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2 ≤ D.gramEigenvalue 1 := by
    rw [D.xi_negative_block_spectrum_spike_and_shallow_bound_gram_sq 1]
    have hSing_nonneg : 0 ≤ D.spikeData.singularValue 1 :=
      D.xi_negative_block_spectrum_spike_and_shallow_bound_singular_nonneg 1
    nlinarith [hLead, hSing_nonneg,
      D.xi_negative_block_spectrum_spike_and_shallow_bound_gap_nonneg]
  have hTail_sq :
      ∀ j : ℕ, 2 ≤ j → D.gramEigenvalue j ≤ ((D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2 := by
    intro j hj
    rw [D.xi_negative_block_spectrum_spike_and_shallow_bound_gram_sq j]
    have hSing_nonneg : 0 ≤ D.spikeData.singularValue j :=
      D.xi_negative_block_spectrum_spike_and_shallow_bound_singular_nonneg j
    have hTail_le : D.spikeData.singularValue j ≤ (D.spikeData.κ : ℝ) * D.spikeData.B := hTail j hj
    nlinarith
  refine ⟨hLead_sq, hTail_sq, ?_, ?_⟩
  · rw [D.xi_negative_block_spectrum_spike_and_shallow_bound_negative_eq 1]
    nlinarith [hLead_sq]
  · intro j hj
    rw [D.xi_negative_block_spectrum_spike_and_shallow_bound_negative_eq j]
    nlinarith [hTail_sq j hj]

end Omega.Zeta
