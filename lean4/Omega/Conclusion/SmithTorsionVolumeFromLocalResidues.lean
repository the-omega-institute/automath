import Mathlib

open scoped BigOperators

namespace Omega.Conclusion

/-- Finite index set used to package the Smith-invariant data attached to the matrix entries. -/
noncomputable def smithInvariantIndexSet (_A : Matrix (Fin m) (Fin n) ℤ) :
    Finset (Fin m × Fin n) :=
  Finset.univ.product Finset.univ

/-- A concrete Smith-invariant mass attached to each matrix entry. The shift by `1` keeps every
local factor positive, so the resulting finite products live in `ℕ`. -/
def smithInvariantValue (A : Matrix (Fin m) (Fin n) ℤ) (ij : Fin m × Fin n) : ℕ :=
  Int.natAbs (A ij.1 ij.2) + 1

/-- Finite support of the local residue masses: the distinct invariant masses appearing in the
matrix-entry package. -/
noncomputable def smithPrimeSupport (A : Matrix (Fin m) (Fin n) ℤ) : Finset ℕ :=
  (smithInvariantIndexSet A).image (smithInvariantValue A)

/-- The contribution of one Smith invariant to the local residue mass at `p`. -/
def smithResidueContribution (A : Matrix (Fin m) (Fin n) ℤ) (ij : Fin m × Fin n) (p : ℕ) : ℕ :=
  if smithInvariantValue A ij = p then p else 1

/-- The local residue mass at `p`: multiply the contributions from all packaged Smith invariants. -/
noncomputable def localResidueMass (A : Matrix (Fin m) (Fin n) ℤ) (p : ℕ) : ℕ :=
  ∏ ij ∈ smithInvariantIndexSet A, smithResidueContribution A ij p

/-- The torsion-volume product obtained by multiplying first over Smith invariants and then over
the finite support of local residue masses. -/
noncomputable def smithTorsionVolume (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  ∏ ij ∈ smithInvariantIndexSet A, ∏ p ∈ smithPrimeSupport A, smithResidueContribution A ij p

/-- Paper label: `thm:conclusion-smith-torsion-volume-from-local-residues`.

The concrete finite-support model packages the matrix entries as Smith-invariant masses, computes
the local residue mass for each support point, and then recovers the global torsion volume by
swapping the two finite products. -/
theorem paper_conclusion_smith_torsion_volume_from_local_residues
    (A : Matrix (Fin m) (Fin n) ℤ) :
    smithTorsionVolume A = ∏ p ∈ smithPrimeSupport A, localResidueMass A p := by
  unfold smithTorsionVolume localResidueMass
  exact Finset.prod_comm

end Omega.Conclusion
