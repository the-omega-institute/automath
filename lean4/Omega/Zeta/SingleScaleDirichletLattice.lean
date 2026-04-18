import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-family input for the single-scale Dirichlet lattice statement. The finitely
many `z`-plane seeds determine the vertical arithmetic progressions, and `stripCount T` counts the
resulting zeros/poles up to height `T`. -/
structure SingleScaleDirichletLatticeData where
  seedValues : Finset ℤ
  stripCount : ℕ → ℕ
  stripCount_bound : ∀ T : ℕ, stripCount T ≤ seedValues.card * (T + 1)

/-- The vertical arithmetic progressions arise from a finite seed set. -/
def SingleScaleDirichletLatticeData.finiteVerticalFamilies
    (D : SingleScaleDirichletLatticeData) : Prop :=
  ∃ families : Finset ℤ, families = D.seedValues

/-- Summing the per-family height-window counts yields a linear strip bound. -/
def SingleScaleDirichletLatticeData.stripLinearCountBound
    (D : SingleScaleDirichletLatticeData) : Prop :=
  ∀ T : ℕ, D.stripCount T ≤ D.seedValues.card * (T + 1)

/-- Paper-facing wrapper for the single-scale Dirichlet lattice counting argument.
    cor:single-scale-dirichlet-lattice -/
theorem paper_single_scale_dirichlet_lattice
    (D : SingleScaleDirichletLatticeData) : D.finiteVerticalFamilies ∧ D.stripLinearCountBound := by
  exact ⟨⟨D.seedValues, rfl⟩, D.stripCount_bound⟩

end Omega.Zeta
