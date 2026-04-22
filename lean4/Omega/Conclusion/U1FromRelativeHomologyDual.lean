import Omega.Conclusion.NoConnectedU1DirectFactor
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete model for the torus-fiber `H₁` lattice. -/
abbrev conclusion_u1_from_relative_homology_dual_torus_fiber_h1 (v : ℕ) := Fin v → ℤ

/-- Concrete model for the relative `H₂` lattice. -/
abbrev conclusion_u1_from_relative_homology_dual_relative_h2 (v : ℕ) := Fin v → ℤ

/-- Concrete model for the target unit circle written additively. -/
abbrev conclusion_u1_from_relative_homology_dual_unit_add_circle := AddCircle (1 : ℝ)

/-- The intrinsic `U(1)^v` phase torus attached to the relative lattice. -/
abbrev conclusion_u1_from_relative_homology_dual_phase_torus (v : ℕ) :=
  Fin v → conclusion_u1_from_relative_homology_dual_unit_add_circle

/-- The Pontryagin dual of the concrete relative lattice. -/
abbrev conclusion_u1_from_relative_homology_dual_character_group (v : ℕ) :=
  conclusion_u1_from_relative_homology_dual_relative_h2 v →+
    conclusion_u1_from_relative_homology_dual_unit_add_circle

/-- Precomposition with the transfer isomorphism identifies the torus-fiber dual with the
relative-homology dual. -/
def conclusion_u1_from_relative_homology_dual_transfer_dual_equiv
    {v : ℕ}
    (τ :
      conclusion_u1_from_relative_homology_dual_torus_fiber_h1 v ≃+
        conclusion_u1_from_relative_homology_dual_relative_h2 v) :
    (conclusion_u1_from_relative_homology_dual_relative_h2 v →+
        conclusion_u1_from_relative_homology_dual_unit_add_circle) ≃
      (conclusion_u1_from_relative_homology_dual_torus_fiber_h1 v →+
        conclusion_u1_from_relative_homology_dual_unit_add_circle) where
  toFun χ := χ.comp τ.toAddMonoidHom
  invFun ψ := ψ.comp τ.symm.toAddMonoidHom
  left_inv χ := by
    ext x
    simp
  right_inv ψ := by
    ext x
    simp

/-- The phase `u ∈ U(1)^v` defines the character obtained by summing the coordinate phases against
the lattice coefficients. -/
noncomputable def conclusion_u1_from_relative_homology_dual_phase_to_character
    {v : ℕ}
    (u : conclusion_u1_from_relative_homology_dual_phase_torus v) :
    conclusion_u1_from_relative_homology_dual_character_group v where
  toFun n := ∑ i, n i • u i
  map_zero' := by simp
  map_add' a b := by
    simp [add_zsmul, Finset.sum_add_distrib]

/-- Recover the coordinate phases from a character by evaluating it on the standard basis. -/
def conclusion_u1_from_relative_homology_dual_character_to_phase
    {v : ℕ}
    (χ : conclusion_u1_from_relative_homology_dual_character_group v) :
    conclusion_u1_from_relative_homology_dual_phase_torus v :=
  fun i => χ (Pi.single i (1 : ℤ))

/-- The Pontryagin dual of `ℤ^v` is canonically `U(1)^v`. -/
noncomputable def conclusion_u1_from_relative_homology_dual_pontryagin_dual_equiv
    (v : ℕ) :
    conclusion_u1_from_relative_homology_dual_character_group v ≃
      conclusion_u1_from_relative_homology_dual_phase_torus v where
  toFun := conclusion_u1_from_relative_homology_dual_character_to_phase
  invFun := conclusion_u1_from_relative_homology_dual_phase_to_character
  left_inv χ := by
    classical
    apply AddMonoidHom.ext
    intro n
    have hdecomp :
        n =
          ∑ i, (Pi.single i (n i) :
            conclusion_u1_from_relative_homology_dual_relative_h2 v) := by
      ext j
      simp [Pi.single_apply]
    have hsingle :
        ∀ i : Fin v,
          (Pi.single i (n i) : conclusion_u1_from_relative_homology_dual_relative_h2 v) =
            n i • (Pi.single i (1 : ℤ) :
              conclusion_u1_from_relative_homology_dual_relative_h2 v) := by
      intro i
      ext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [hij]
    calc
      conclusion_u1_from_relative_homology_dual_phase_to_character
          (conclusion_u1_from_relative_homology_dual_character_to_phase χ) n
          = ∑ i, n i • χ (Pi.single i (1 : ℤ)) := by
              simp [conclusion_u1_from_relative_homology_dual_character_to_phase,
                conclusion_u1_from_relative_homology_dual_phase_to_character]
      _ = ∑ i, χ (Pi.single i (n i) :
            conclusion_u1_from_relative_homology_dual_relative_h2 v) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hsingle i, map_zsmul]
      _ = χ
            (∑ i, (Pi.single i (n i) :
              conclusion_u1_from_relative_homology_dual_relative_h2 v)) := by
              simpa using
                (map_sum χ Finset.univ
                  (fun i => (Pi.single i (n i) :
                    conclusion_u1_from_relative_homology_dual_relative_h2 v))).symm
      _ = χ n := by
              rw [hdecomp]
              congr 1
              ext j
              simp [Pi.single_apply]
  right_inv u := by
    ext i
    simp [conclusion_u1_from_relative_homology_dual_character_to_phase,
      conclusion_u1_from_relative_homology_dual_phase_to_character]

/-- Paper label: `thm:conclusion-u1-from-relative-homology-dual`. The transfer identifies the
torus-fiber `H₁` lattice with the relative `H₂` lattice, the latter has Pontryagin dual `U(1)^v`,
and this dual phase source remains external to the connected automorphism side because that side
has no connected `U(1)` direct factor. -/
theorem paper_conclusion_u1_from_relative_homology_dual
    (v : ℕ)
    (τ :
      conclusion_u1_from_relative_homology_dual_torus_fiber_h1 v ≃+
        conclusion_u1_from_relative_homology_dual_relative_h2 v)
    (D : ConnectedAutomorphismDecompositionData) :
    Nonempty
      ((conclusion_u1_from_relative_homology_dual_relative_h2 v →+
          conclusion_u1_from_relative_homology_dual_unit_add_circle) ≃
        (conclusion_u1_from_relative_homology_dual_torus_fiber_h1 v →+
          conclusion_u1_from_relative_homology_dual_unit_add_circle)) ∧
      Nonempty
        (conclusion_u1_from_relative_homology_dual_character_group v ≃
          conclusion_u1_from_relative_homology_dual_phase_torus v) ∧
      D.noConnectedU1DirectFactor := by
  refine ⟨⟨conclusion_u1_from_relative_homology_dual_transfer_dual_equiv τ⟩,
    ⟨conclusion_u1_from_relative_homology_dual_pontryagin_dual_equiv v⟩, ?_⟩
  exact paper_conclusion_no_connected_u1_direct_factor D

end Omega.Conclusion
