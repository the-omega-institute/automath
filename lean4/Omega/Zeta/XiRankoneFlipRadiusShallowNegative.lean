import Mathlib.Tactic
import Omega.Zeta.XiHankelSpikeSingularSpectrumSeparation

namespace Omega.Zeta

/-- Concrete data for the rank-one shallow-negative flip radius package. The smallest Gram
eigenvalue is modeled by the square of a tail singular value, the rank-one projector has operator
norm one, and the negative inertia starts with at least one shallow negative direction. -/
structure xi_rankone_flip_radius_shallow_negative_data where
  spikeData : XiHankelSpikeSingularSpectrumData
  tailIndex : ℕ
  htailIndex : 2 ≤ tailIndex
  htailSingular_nonneg : 0 ≤ spikeData.singularValue tailIndex
  initialNegativeDirections : ℕ
  hinitialNegativeDirections : 1 ≤ initialNegativeDirections
  rankOneProjectorOpNorm : ℝ
  rankOneProjectorOpNorm_eq_one : rankOneProjectorOpNorm = 1

/-- The smallest Gram eigenvalue carried by the shallow tail direction. -/
def xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue
    (D : xi_rankone_flip_radius_shallow_negative_data) : ℝ :=
  D.spikeData.singularValue D.tailIndex ^ 2

/-- The operator norm of the Hermitian rank-one perturbation `Δ = λ_min vv*`. -/
def xi_rankone_flip_radius_shallow_negative_rankOnePerturbationOpNorm
    (D : xi_rankone_flip_radius_shallow_negative_data) : ℝ :=
  xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue D * D.rankOneProjectorOpNorm

/-- The negative inertia after the shallow rank-one direction is flipped to zero. -/
def xi_rankone_flip_radius_shallow_negative_remainingNegativeDirections
    (D : xi_rankone_flip_radius_shallow_negative_data) : ℕ :=
  D.initialNegativeDirections - 1

/-- Paper-facing shallow-negative flip package: the singular-spectrum separation holds, the
rank-one perturbation norm equals the smallest Gram eigenvalue, one negative direction is removed
exactly, and the perturbation radius is bounded by the tail singular-value envelope. -/
def xi_rankone_flip_radius_shallow_negative_statement
    (D : xi_rankone_flip_radius_shallow_negative_data) : Prop :=
  D.spikeData.singularSpectrumSeparated ∧
    0 ≤ xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue D ∧
    xi_rankone_flip_radius_shallow_negative_rankOnePerturbationOpNorm D =
      xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue D ∧
    xi_rankone_flip_radius_shallow_negative_remainingNegativeDirections D + 1 =
      D.initialNegativeDirections ∧
    xi_rankone_flip_radius_shallow_negative_rankOnePerturbationOpNorm D ≤
      ((D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2

/-- Paper label: `prop:xi-rankone-flip-radius-shallow-negative`. -/
theorem paper_xi_rankone_flip_radius_shallow_negative
    (D : xi_rankone_flip_radius_shallow_negative_data) :
    xi_rankone_flip_radius_shallow_negative_statement D := by
  have hSpike := paper_xi_hankel_spike_singular_spectrum_separation D.spikeData
  rcases hSpike with ⟨_, hTail⟩
  have hTailBound : D.spikeData.singularValue D.tailIndex ≤ (D.spikeData.κ : ℝ) * D.spikeData.B :=
    hTail D.tailIndex D.htailIndex
  have hκB_nonneg : 0 ≤ (D.spikeData.κ : ℝ) * D.spikeData.B := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le D.spikeData.κ) D.spikeData.hB_nonneg
  have hSmall_nonneg :
      0 ≤ xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue D := by
    unfold xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue
    positivity
  have hRemaining :
      xi_rankone_flip_radius_shallow_negative_remainingNegativeDirections D + 1 =
        D.initialNegativeDirections := by
    unfold xi_rankone_flip_radius_shallow_negative_remainingNegativeDirections
    exact Nat.sub_add_cancel D.hinitialNegativeDirections
  have hSquareBound :
      xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue D ≤
        ((D.spikeData.κ : ℝ) * D.spikeData.B) ^ 2 := by
    unfold xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue
    nlinarith [D.htailSingular_nonneg, hTailBound, hκB_nonneg]
  refine ⟨paper_xi_hankel_spike_singular_spectrum_separation D.spikeData, hSmall_nonneg, ?_,
    hRemaining, ?_⟩
  · unfold xi_rankone_flip_radius_shallow_negative_rankOnePerturbationOpNorm
      xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue
    rw [D.rankOneProjectorOpNorm_eq_one]
    ring
  · have hNormEq :
        xi_rankone_flip_radius_shallow_negative_rankOnePerturbationOpNorm D =
          xi_rankone_flip_radius_shallow_negative_smallestGramEigenvalue D := by
      unfold xi_rankone_flip_radius_shallow_negative_rankOnePerturbationOpNorm
      rw [D.rankOneProjectorOpNorm_eq_one]
      ring
    rw [hNormEq]
    exact hSquareBound

end Omega.Zeta
