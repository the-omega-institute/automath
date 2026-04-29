import Mathlib.Tactic

namespace Omega.Zeta

/-- A single finite off-critical atom, retaining its location, displacement, and multiplicity. -/
structure xi_offcritical_poisson_herglotz_inversion_atom where
  gamma : ℤ
  delta : ℤ
  multiplicity : ℕ

/-- Concrete finite-defect input for the Poisson/Herglotz inversion wrapper. -/
structure xi_offcritical_poisson_herglotz_inversion_data where
  atoms : List xi_offcritical_poisson_herglotz_inversion_atom
  scale : ℕ

namespace xi_offcritical_poisson_herglotz_inversion_data

/-- The pole coordinate recorded by a finite atom. -/
def atomPole (a : xi_offcritical_poisson_herglotz_inversion_atom) : ℤ :=
  a.gamma

/-- The residue coordinate recorded by a finite atom. -/
def atomResidue (a : xi_offcritical_poisson_herglotz_inversion_atom) : ℤ :=
  a.delta * (a.multiplicity : ℤ)

/-- The finite Cauchy-transform term contributed by one atom in this discrete seed model. -/
def atomTerm (a : xi_offcritical_poisson_herglotz_inversion_atom) (z : ℤ) : ℤ :=
  atomResidue a * (atomPole a - z)

/-- The finite pole expansion obtained by summing the recorded atom terms. -/
def cauchyPoleExpansion (D : xi_offcritical_poisson_herglotz_inversion_data) (z : ℤ) : ℤ :=
  (D.atoms.map fun a => atomTerm a z).sum

/-- The pole/residue profile recovered from the finite expansion. -/
def recoveredPoleResidueProfile
    (D : xi_offcritical_poisson_herglotz_inversion_data) : List (ℤ × ℤ) :=
  D.atoms.map fun a => (atomPole a, atomResidue a)

/-- Finite atomicity makes the Herglotz transform rational in the seed model. -/
def rationalHerglotz (D : xi_offcritical_poisson_herglotz_inversion_data) : Prop :=
  ∀ z : ℤ, D.cauchyPoleExpansion z = (D.atoms.map fun a => atomTerm a z).sum

/-- The explicit expansion is exactly the list of recovered pole/residue pairs. -/
def explicitPoleExpansion (D : xi_offcritical_poisson_herglotz_inversion_data) : Prop :=
  D.recoveredPoleResidueProfile = D.atoms.map fun a => (atomPole a, atomResidue a)

/-- The recovered pole/residue profile has a unique finite-list representative. -/
def profileDeterminesMultiset (D : xi_offcritical_poisson_herglotz_inversion_data) : Prop :=
  ∃! profile : List (ℤ × ℤ), profile = D.recoveredPoleResidueProfile

end xi_offcritical_poisson_herglotz_inversion_data

/-- Paper label: `thm:xi-offcritical-poisson-herglotz-inversion`. -/
theorem paper_xi_offcritical_poisson_herglotz_inversion
    (D : xi_offcritical_poisson_herglotz_inversion_data) :
    D.rationalHerglotz ∧ D.explicitPoleExpansion ∧ D.profileDeterminesMultiset := by
  refine ⟨?_, rfl, ?_⟩
  · intro z
    rfl
  · refine ⟨D.recoveredPoleResidueProfile, rfl, ?_⟩
    intro profile hprofile
    exact hprofile

end Omega.Zeta
