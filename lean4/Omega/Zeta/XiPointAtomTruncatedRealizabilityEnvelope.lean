import Mathlib.Tactic

namespace Omega.Zeta

open Set

/-- Point-mass values attained by the `N`th truncated feasible set. -/
def xi_point_atom_truncated_realizability_envelope_feasible_values
    {MomentMeasure : Type*} (feasible : ℕ → Set MomentMeasure)
    (pointMass : MomentMeasure → ℝ) (N : ℕ) : Set ℝ :=
  pointMass '' feasible N

/-- The Cauchy-style convergence conclusion used for the lower envelope. -/
def xi_point_atom_truncated_realizability_envelope_converges_to
    (lower : ℕ → ℝ) (atom : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → atom - ε < lower n ∧ lower n ≤ atom

/-- Concrete statement package for the truncated point-atom realizability envelope.

The feasible sets are nested by increasing truncation order, the original measure remains feasible
at every order, each `lower N` is the greatest lower bound of the point masses over the `N`th
feasible set, and the determinacy/compactness input is recorded as eventual approximation of the
original point mass from below. -/
def xi_point_atom_truncated_realizability_envelope_statement : Prop :=
  ∀ {MomentMeasure : Type*} (feasible : ℕ → Set MomentMeasure)
    (pointMass : MomentMeasure → ℝ) (original : MomentMeasure) (lower : ℕ → ℝ),
    (∀ N : ℕ, feasible (N + 1) ⊆ feasible N) →
    (∀ N : ℕ, original ∈ feasible N) →
    (∀ N : ℕ,
      IsGLB
        (xi_point_atom_truncated_realizability_envelope_feasible_values feasible pointMass N)
        (lower N)) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, pointMass original - ε < lower N) →
      Monotone lower ∧
        (∀ N : ℕ, lower N ≤ pointMass original) ∧
        xi_point_atom_truncated_realizability_envelope_converges_to lower (pointMass original)

/-- Paper label: `thm:xi-point-atom-truncated-realizability-envelope`. -/
theorem paper_xi_point_atom_truncated_realizability_envelope :
    xi_point_atom_truncated_realizability_envelope_statement := by
  intro MomentMeasure feasible pointMass original lower hnested horiginal hlower happrox
  have hmono : Monotone lower := by
    intro N M hNM
    induction M, hNM using Nat.le_induction with
    | base => exact le_rfl
    | succ M hNM hstep =>
        have hsucc : lower M ≤ lower (M + 1) := by
          refine (hlower (M + 1)).2 ?_
          intro x hx
          rcases hx with ⟨ν, hν, rfl⟩
          exact (hlower M).1 ⟨ν, hnested M hν, rfl⟩
        exact le_trans hstep hsucc
  have hupper : ∀ N : ℕ, lower N ≤ pointMass original := by
    intro N
    exact (hlower N).1 ⟨original, horiginal N, rfl⟩
  refine ⟨hmono, hupper, ?_⟩
  intro ε hε
  rcases happrox ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨lt_of_lt_of_le hN (hmono hn), hupper n⟩

end Omega.Zeta
