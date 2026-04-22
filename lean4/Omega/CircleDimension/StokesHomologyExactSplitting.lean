import Mathlib.Tactic

namespace Omega.CircleDimension.StokesHomologyExactSplitting

/-- Projection to the `ℤ^u` factor. -/
def stokesProjection (u v : ℕ) :
    ((Fin u → ℤ) × (Fin v → ℤ)) → (Fin u → ℤ) :=
  fun p => p.1

/-- Inclusion of the boundary factor as the second direct summand. -/
def stokesBoundaryInclusion (u v : ℕ) :
    (Fin v → ℤ) → ((Fin u → ℤ) × (Fin v → ℤ)) :=
  fun y => (0, y)

/-- Splitting section of the projection. -/
def stokesSection (u v : ℕ) :
    (Fin u → ℤ) → ((Fin u → ℤ) × (Fin v → ℤ)) :=
  fun x => (x, 0)

theorem stokesBoundaryInclusion_injective (u v : ℕ) :
    Function.Injective (stokesBoundaryInclusion u v) := by
  intro y₁ y₂ h
  simpa [stokesBoundaryInclusion] using congrArg Prod.snd h

theorem stokesProjection_surjective (u v : ℕ) :
    Function.Surjective (stokesProjection u v) := by
  intro x
  exact ⟨stokesSection u v x, rfl⟩

theorem stokes_range_eq_kernel (u v : ℕ) :
    Set.range (stokesBoundaryInclusion u v) =
      {p | stokesProjection u v p = 0} := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hp
    refine ⟨p.2, ?_⟩
    rcases p with ⟨x, y⟩
    dsimp [stokesProjection] at hp
    dsimp [stokesBoundaryInclusion]
    cases hp
    rfl

theorem stokesProjection_section (u v : ℕ) (x : Fin u → ℤ) :
    stokesProjection u v (stokesSection u v x) = x := by
  rfl

theorem stokes_split_decomposition (u v : ℕ) (p : (Fin u → ℤ) × (Fin v → ℤ)) :
    stokesSection u v (stokesProjection u v p) +
        stokesBoundaryInclusion u v p.2 = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · funext i
    simp [stokesSection, stokesProjection, stokesBoundaryInclusion]
  · funext i
    simp [stokesSection, stokesProjection, stokesBoundaryInclusion]

/-- Paper seed: the low-dimensional Stokes exact sequence is modeled by the split short
    exact sequence `0 → ℤ^v → ℤ^u × ℤ^v → ℤ^u → 0`.
    prop:cdim-stokes-homology-exact-splitting -/
theorem paper_cdim_stokes_homology_exact_splitting_seeds (u v : ℕ) :
    Function.Injective (stokesBoundaryInclusion u v) ∧
      Function.Surjective (stokesProjection u v) ∧
      Set.range (stokesBoundaryInclusion u v) =
        {p | stokesProjection u v p = 0} ∧
      (∀ x, stokesProjection u v (stokesSection u v x) = x) ∧
      (∀ p,
        stokesSection u v (stokesProjection u v p) +
          stokesBoundaryInclusion u v p.2 = p) := by
  refine ⟨stokesBoundaryInclusion_injective u v, stokesProjection_surjective u v,
    stokes_range_eq_kernel u v, stokesProjection_section u v, stokes_split_decomposition u v⟩

/-- Paper-facing split short exact sequence statement for Stokes homology.
    prop:cdim-stokes-homology-exact-splitting -/
theorem paper_cdim_stokes_homology_exact_splitting (u v : ℕ) :
    Function.Injective (stokesBoundaryInclusion u v) ∧
      Function.Surjective (stokesProjection u v) ∧
      Set.range (stokesBoundaryInclusion u v) =
        {p | stokesProjection u v p = 0} ∧
      (∀ x, stokesProjection u v (stokesSection u v x) = x) ∧
      (∀ p : (Fin u → ℤ) × (Fin v → ℤ),
        ∃ x : Fin u → ℤ, ∃ y : Fin v → ℤ,
          p = stokesSection u v x + stokesBoundaryInclusion u v y) := by
  rcases paper_cdim_stokes_homology_exact_splitting_seeds u v with
    ⟨hinj, hsurj, hexact, hsection, hsplit⟩
  refine ⟨hinj, hsurj, hexact, hsection, ?_⟩
  intro p
  refine ⟨stokesProjection u v p, p.2, ?_⟩
  symm
  exact hsplit p

end Omega.CircleDimension.StokesHomologyExactSplitting
