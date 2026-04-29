import Mathlib.Tactic

namespace Omega.Conclusion

/-- One finite Euler atom in the completed-slice calculation. -/
structure conclusion_completed_slice_balanced_atoms_become_constants_atom where
  conclusion_completed_slice_balanced_atoms_become_constants_atom_energy : ℕ
  conclusion_completed_slice_balanced_atoms_become_constants_atom_length : ℕ
  conclusion_completed_slice_balanced_atoms_become_constants_atom_multiplicity : ℕ

/-- Concrete finite atom data for the completed-slice specialization.  The `scale` map models
`x ↦ L^x`; the theorem below only needs equality of its exponents. -/
structure conclusion_completed_slice_balanced_atoms_become_constants_data where
  conclusion_completed_slice_balanced_atoms_become_constants_atoms :
    List conclusion_completed_slice_balanced_atoms_become_constants_atom
  conclusion_completed_slice_balanced_atoms_become_constants_scale : ℝ → ℝ
  conclusion_completed_slice_balanced_atoms_become_constants_coreSlice : ℝ → ℝ

namespace conclusion_completed_slice_balanced_atoms_become_constants_atom

/-- Atom energy, written as a prefixed accessor to avoid root-name clashes. -/
def conclusion_completed_slice_balanced_atoms_become_constants_energy
    (a : conclusion_completed_slice_balanced_atoms_become_constants_atom) : ℕ :=
  a.conclusion_completed_slice_balanced_atoms_become_constants_atom_energy

/-- Atom length, written as a prefixed accessor to avoid root-name clashes. -/
def conclusion_completed_slice_balanced_atoms_become_constants_length
    (a : conclusion_completed_slice_balanced_atoms_become_constants_atom) : ℕ :=
  a.conclusion_completed_slice_balanced_atoms_become_constants_atom_length

/-- Atom multiplicity, written as a prefixed accessor to avoid root-name clashes. -/
def conclusion_completed_slice_balanced_atoms_become_constants_multiplicity
    (a : conclusion_completed_slice_balanced_atoms_become_constants_atom) : ℕ :=
  a.conclusion_completed_slice_balanced_atoms_become_constants_atom_multiplicity

end conclusion_completed_slice_balanced_atoms_become_constants_atom

namespace conclusion_completed_slice_balanced_atoms_become_constants_data

open conclusion_completed_slice_balanced_atoms_become_constants_atom

/-- The raw atom factor after substituting `z_L(s)=L^{-s}` and `u_L(s)=L^{2s-1}`,
but before collecting the exponent. -/
noncomputable def originalAtomFactor
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data)
    (a : conclusion_completed_slice_balanced_atoms_become_constants_atom) (s : ℝ) : ℝ :=
  (1 -
      D.conclusion_completed_slice_balanced_atoms_become_constants_scale
        (((2 * s - 1) *
            (a.conclusion_completed_slice_balanced_atoms_become_constants_energy : ℝ)) +
          ((-s) *
            (a.conclusion_completed_slice_balanced_atoms_become_constants_length : ℝ)))) ^
    a.conclusion_completed_slice_balanced_atoms_become_constants_multiplicity

/-- The collected completed-slice atom factor
`(1-L^{-E}L^{(2E-ell)s})^m`, with `scale` standing for `L^·`. -/
noncomputable def completedAtomFactor
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data)
    (a : conclusion_completed_slice_balanced_atoms_become_constants_atom) (s : ℝ) : ℝ :=
  (1 -
      D.conclusion_completed_slice_balanced_atoms_become_constants_scale
        (-(a.conclusion_completed_slice_balanced_atoms_become_constants_energy : ℝ) +
          ((2 * (a.conclusion_completed_slice_balanced_atoms_become_constants_energy : ℝ)) -
              (a.conclusion_completed_slice_balanced_atoms_become_constants_length : ℝ)) *
            s)) ^
    a.conclusion_completed_slice_balanced_atoms_become_constants_multiplicity

/-- Product of the raw atom factors. -/
noncomputable def originalAtomProduct
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data) (s : ℝ) : ℝ :=
  (D.conclusion_completed_slice_balanced_atoms_become_constants_atoms.map
      (fun a => D.originalAtomFactor a s)).prod

/-- Product of the collected completed-slice atom factors. -/
noncomputable def completedAtomProduct
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data) (s : ℝ) : ℝ :=
  (D.conclusion_completed_slice_balanced_atoms_become_constants_atoms.map
      (fun a => D.completedAtomFactor a s)).prod

/-- The completed slice before the atom exponents are collected. -/
noncomputable def completedSlice
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data) (s : ℝ) : ℝ :=
  D.originalAtomProduct s *
    D.conclusion_completed_slice_balanced_atoms_become_constants_coreSlice s

/-- The completed-slice factorization as a finite product times the core slice. -/
def completedSliceFactorization
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data) : Prop :=
  ∀ s : ℝ,
    D.completedSlice s =
      D.completedAtomProduct s *
        D.conclusion_completed_slice_balanced_atoms_become_constants_coreSlice s

/-- Balanced atoms, `ell = 2E`, have an `s`-independent completed-slice factor. -/
def balancedAtomConstantization
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data) : Prop :=
  ∀ a ∈ D.conclusion_completed_slice_balanced_atoms_become_constants_atoms,
    a.conclusion_completed_slice_balanced_atoms_become_constants_length =
        2 * a.conclusion_completed_slice_balanced_atoms_become_constants_energy →
      ∀ s : ℝ, D.completedAtomFactor a s = D.completedAtomFactor a 0

lemma conclusion_completed_slice_balanced_atoms_become_constants_atom_factor_formula
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data)
    (a : conclusion_completed_slice_balanced_atoms_become_constants_atom) (s : ℝ) :
    D.originalAtomFactor a s = D.completedAtomFactor a s := by
  have harg :
      ((2 * s - 1) *
            (a.conclusion_completed_slice_balanced_atoms_become_constants_energy : ℝ)) +
          -(s * (a.conclusion_completed_slice_balanced_atoms_become_constants_length : ℝ)) =
        -(a.conclusion_completed_slice_balanced_atoms_become_constants_energy : ℝ) +
          ((2 * (a.conclusion_completed_slice_balanced_atoms_become_constants_energy : ℝ)) -
              (a.conclusion_completed_slice_balanced_atoms_become_constants_length : ℝ)) *
            s := by
    ring
  simp [originalAtomFactor, completedAtomFactor, harg]

lemma conclusion_completed_slice_balanced_atoms_become_constants_product_formula
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data) (s : ℝ) :
    D.originalAtomProduct s = D.completedAtomProduct s := by
  simp [originalAtomProduct, completedAtomProduct,
    conclusion_completed_slice_balanced_atoms_become_constants_atom_factor_formula]

lemma conclusion_completed_slice_balanced_atoms_become_constants_balanced_factor
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data)
    (a : conclusion_completed_slice_balanced_atoms_become_constants_atom)
    (hbalanced :
      a.conclusion_completed_slice_balanced_atoms_become_constants_length =
        2 * a.conclusion_completed_slice_balanced_atoms_become_constants_energy)
    (s : ℝ) :
    D.completedAtomFactor a s = D.completedAtomFactor a 0 := by
  have hlength :
      (a.conclusion_completed_slice_balanced_atoms_become_constants_length : ℝ) =
        2 * (a.conclusion_completed_slice_balanced_atoms_become_constants_energy : ℝ) := by
    rw [hbalanced]
    norm_num
  simp [completedAtomFactor, hlength]

end conclusion_completed_slice_balanced_atoms_become_constants_data

open conclusion_completed_slice_balanced_atoms_become_constants_data

/-- Paper label: `thm:conclusion-completed-slice-balanced-atoms-become-constants`. -/
theorem paper_conclusion_completed_slice_balanced_atoms_become_constants
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data) :
    D.completedSliceFactorization ∧ D.balancedAtomConstantization := by
  constructor
  · intro s
    rw [completedSlice]
    rw [conclusion_completed_slice_balanced_atoms_become_constants_product_formula]
  · intro a ha hbalanced s
    exact conclusion_completed_slice_balanced_atoms_become_constants_balanced_factor D a hbalanced s

/-- Paper label:
`thm:conclusion-completed-slice-normalized-kernel-balanced-atoms`. -/
theorem paper_conclusion_completed_slice_normalized_kernel_balanced_atoms
    (D : conclusion_completed_slice_balanced_atoms_become_constants_data)
    (hbalanced :
      ∀ a ∈ D.conclusion_completed_slice_balanced_atoms_become_constants_atoms,
        a.conclusion_completed_slice_balanced_atoms_become_constants_length =
          2 * a.conclusion_completed_slice_balanced_atoms_become_constants_energy) :
    (∀ s : ℝ, D.completedAtomProduct s = D.completedAtomProduct (1 / 2)) ∧
      ∀ s : ℝ,
        D.completedSlice s =
          D.completedAtomProduct (1 / 2) *
            D.conclusion_completed_slice_balanced_atoms_become_constants_coreSlice s := by
  have hconst : ∀ s : ℝ, D.completedAtomProduct s = D.completedAtomProduct (1 / 2) := by
    intro s
    have hfactor :
        ∀ a ∈ D.conclusion_completed_slice_balanced_atoms_become_constants_atoms,
          D.completedAtomFactor a s = D.completedAtomFactor a (1 / 2) := by
      intro a ha
      have hs :=
        conclusion_completed_slice_balanced_atoms_become_constants_balanced_factor D a
          (hbalanced a ha) s
      have hhalf :=
        conclusion_completed_slice_balanced_atoms_become_constants_balanced_factor D a
          (hbalanced a ha) (1 / 2)
      exact hs.trans hhalf.symm
    have hprod :
        ∀ l : List conclusion_completed_slice_balanced_atoms_become_constants_atom,
          (∀ a ∈ l, D.completedAtomFactor a s = D.completedAtomFactor a (1 / 2)) →
            (l.map (fun a => D.completedAtomFactor a s)).prod =
              (l.map (fun a => D.completedAtomFactor a (1 / 2))).prod := by
      intro l
      induction l with
      | nil =>
          intro _h
          simp
      | cons a t ih =>
          intro h
          simp only [List.mem_cons] at h
          simp [h a (Or.inl rfl), ih (fun b hb => h b (Or.inr hb))]
    simpa [completedAtomProduct] using
      hprod D.conclusion_completed_slice_balanced_atoms_become_constants_atoms hfactor
  constructor
  · exact hconst
  · intro s
    rw [completedSlice]
    rw [conclusion_completed_slice_balanced_atoms_become_constants_product_formula]
    rw [hconst s]

end Omega.Conclusion
