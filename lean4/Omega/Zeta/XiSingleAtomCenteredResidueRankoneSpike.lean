import Omega.Zeta.XiAtomicCenteredResidueSimplex

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-single-atom-centered-residue-rankone-spike`. -/
theorem paper_xi_single_atom_centered_residue_rankone_spike (m : Nat) (hm : 2 <= m)
    (ell : Fin m) :
    (∑ r : Fin m, Omega.Zeta.atomicCenteredResidueVector m ell r = 0) ∧
      Omega.Zeta.atomicCenteredResidueVector m ell ell = (2 : ℤ) * (m : ℤ) - 2 ∧
      (∀ r : Fin m, r ≠ ell → Omega.Zeta.atomicCenteredResidueVector m ell r = -2) ∧
      Omega.Zeta.atomicCenteredResidueInner
          (Omega.Zeta.atomicCenteredResidueVector m ell)
          (Omega.Zeta.atomicCenteredResidueVector m ell) =
        (4 : ℤ) * (m : ℤ) * ((m : ℤ) - 1) := by
  have hsimplex := paper_xi_time_part65c_atomic_centered_residue_simplex m hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hsimplex.1 ell
  · simp [atomicCenteredResidueVector]
  · intro r hr
    simp [atomicCenteredResidueVector, hr]
  · simpa using hsimplex.2 ell ell

end Omega.Zeta
