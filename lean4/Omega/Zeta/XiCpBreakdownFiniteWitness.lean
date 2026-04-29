import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite-channel symbol whose complete positivity is tested by all finite Toeplitz
quadratic truncations. -/
structure xi_cp_breakdown_finite_witness_data where
  xi_cp_breakdown_finite_witness_channelCount : ℕ
  xi_cp_breakdown_finite_witness_channelWeight :
    Fin (xi_cp_breakdown_finite_witness_channelCount + 1) → ℝ

namespace xi_cp_breakdown_finite_witness_data

def xi_cp_breakdown_finite_witness_blockToeplitzQuadratic
    (D : xi_cp_breakdown_finite_witness_data) (N : ℕ)
    (χ : Fin (D.xi_cp_breakdown_finite_witness_channelCount + 1))
    (v : Fin (N + 1) → ℝ) : ℝ :=
  D.xi_cp_breakdown_finite_witness_channelWeight χ * ∑ i : Fin (N + 1), v i ^ 2

def xi_cp_breakdown_finite_witness_blockToeplitzPsd
    (D : xi_cp_breakdown_finite_witness_data) (N : ℕ)
    (χ : Fin (D.xi_cp_breakdown_finite_witness_channelCount + 1)) : Prop :=
  ∀ v : Fin (N + 1) → ℝ,
    0 ≤ D.xi_cp_breakdown_finite_witness_blockToeplitzQuadratic N χ v

def xi_cp_breakdown_finite_witness_completePositive
    (D : xi_cp_breakdown_finite_witness_data) : Prop :=
  ∀ N : ℕ, ∀ χ : Fin (D.xi_cp_breakdown_finite_witness_channelCount + 1),
    D.xi_cp_breakdown_finite_witness_blockToeplitzPsd N χ

def xi_cp_breakdown_finite_witness_negativeWitness
    (D : xi_cp_breakdown_finite_witness_data) : Prop :=
  ∃ (N : ℕ) (χ : Fin (D.xi_cp_breakdown_finite_witness_channelCount + 1))
      (v : Fin (N + 1) → ℝ),
    D.xi_cp_breakdown_finite_witness_blockToeplitzQuadratic N χ v < 0

/-- If complete positivity fails, a finite Toeplitz order and channel carry a negative witness. -/
def statement (D : xi_cp_breakdown_finite_witness_data) : Prop :=
  ¬ D.xi_cp_breakdown_finite_witness_completePositive →
    D.xi_cp_breakdown_finite_witness_negativeWitness

end xi_cp_breakdown_finite_witness_data

/-- Paper label: `cor:xi-cp-breakdown-finite-witness`. -/
theorem paper_xi_cp_breakdown_finite_witness
    (D : xi_cp_breakdown_finite_witness_data) : D.statement := by
  classical
  rw [xi_cp_breakdown_finite_witness_data.statement]
  intro hbreak
  dsimp [
    xi_cp_breakdown_finite_witness_data.xi_cp_breakdown_finite_witness_completePositive,
    xi_cp_breakdown_finite_witness_data.xi_cp_breakdown_finite_witness_blockToeplitzPsd
  ] at hbreak
  push_neg at hbreak
  rcases hbreak with ⟨N, χ, v, hv⟩
  unfold xi_cp_breakdown_finite_witness_data.xi_cp_breakdown_finite_witness_negativeWitness
  exact ⟨N, χ, v, hv⟩

end Omega.Zeta
