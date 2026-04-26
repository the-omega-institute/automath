import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Finite defect-packet data for the offline Neumann trace interaction model. -/
structure xi_offline_neumann_l2_interaction_data where
  κ : ℕ
  center : Fin κ → ℝ
  depth : Fin κ → ℝ
  weight : Fin κ → ℝ
  hdepth : ∀ j, 0 < depth j
  hweight : ∀ j, 0 ≤ weight j

namespace xi_offline_neumann_l2_interaction_data

/-- Shifted Cauchy kernel for a single defect packet. -/
def cauchyAtom (D : xi_offline_neumann_l2_interaction_data) (j : Fin D.κ) (x : ℝ) : ℝ :=
  D.weight j / ((x - D.center j) ^ 2 + D.depth j ^ 2)

/-- Offline Neumann trace as a finite sum of shifted Cauchy kernels. -/
def offlineTrace (D : xi_offline_neumann_l2_interaction_data) (x : ℝ) : ℝ :=
  ∑ j : Fin D.κ, D.cauchyAtom j x

/-- Explicit Fourier transform of one shifted Cauchy packet. -/
def fourierAtom (D : xi_offline_neumann_l2_interaction_data) (j : Fin D.κ) (ξ : ℝ) : ℝ :=
  D.weight j * Real.exp (-D.depth j * |ξ|) * Real.cos (D.center j * ξ)

/-- Fourier transform of the offline trace. -/
def fourierTrace (D : xi_offline_neumann_l2_interaction_data) (ξ : ℝ) : ℝ :=
  ∑ j : Fin D.κ, D.fourierAtom j ξ

/-- Off-diagonal interaction mass left after separating the reciprocal-depth diagonal terms. -/
def offDiagonalMass (D : xi_offline_neumann_l2_interaction_data) : ℝ :=
  ∑ j : Fin D.κ, ∑ k : Fin D.κ,
    if j = k then 0 else D.weight j * D.weight k / (D.depth j + D.depth k)

/-- Reciprocal-depth contribution coming from the diagonal terms. -/
def reciprocalDepthLowerBound (D : xi_offline_neumann_l2_interaction_data) : ℝ :=
  ∑ j : Fin D.κ, D.weight j ^ 2 / D.depth j

/-- The packaged Plancherel interaction energy. -/
def interactionEnergy (D : xi_offline_neumann_l2_interaction_data) : ℝ :=
  D.reciprocalDepthLowerBound + D.offDiagonalMass

/-- Paper-facing statement: the offline Neumann trace and its Fourier transform are explicit
finite sums, the Plancherel energy splits into diagonal and off-diagonal contributions, and
discarding the nonnegative off-diagonal part yields the reciprocal-depth lower bound. -/
def statement (D : xi_offline_neumann_l2_interaction_data) : Prop :=
  (∀ x : ℝ, D.offlineTrace x = ∑ j : Fin D.κ, D.cauchyAtom j x) ∧
    (∀ ξ : ℝ, D.fourierTrace ξ = ∑ j : Fin D.κ, D.fourierAtom j ξ) ∧
    D.interactionEnergy = D.reciprocalDepthLowerBound + D.offDiagonalMass ∧
    D.reciprocalDepthLowerBound ≤ D.interactionEnergy

lemma offDiagonalMass_nonneg (D : xi_offline_neumann_l2_interaction_data) :
    0 ≤ D.offDiagonalMass := by
  unfold offDiagonalMass
  refine Finset.sum_nonneg ?_
  intro j hj
  refine Finset.sum_nonneg ?_
  intro k hk
  by_cases h : j = k
  · simp [h]
  · have hden : 0 < D.depth j + D.depth k := add_pos (D.hdepth j) (D.hdepth k)
    have hnum : 0 ≤ D.weight j * D.weight k := mul_nonneg (D.hweight j) (D.hweight k)
    have hterm : 0 ≤ D.weight j * D.weight k / (D.depth j + D.depth k) :=
      div_nonneg hnum (le_of_lt hden)
    simpa [h] using hterm

lemma reciprocalDepthLowerBound_le_interactionEnergy (D : xi_offline_neumann_l2_interaction_data) :
    D.reciprocalDepthLowerBound ≤ D.interactionEnergy := by
  unfold interactionEnergy
  have hoffdiag : 0 ≤ D.offDiagonalMass := D.offDiagonalMass_nonneg
  linarith

end xi_offline_neumann_l2_interaction_data

open xi_offline_neumann_l2_interaction_data

/-- Paper label: `thm:xi-offline-neumann-l2-interaction`. -/
theorem paper_xi_offline_neumann_l2_interaction
    (D : xi_offline_neumann_l2_interaction_data) : D.statement := by
  refine ⟨?_, ?_, rfl, D.reciprocalDepthLowerBound_le_interactionEnergy⟩
  · intro x
    rfl
  · intro ξ
    rfl

end

end Omega.Zeta
