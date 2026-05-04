import Omega.Zeta.XiAtomicCenteredResidueSimplex

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part77-atomic-centered-residue-tight-frame`. -/
theorem paper_xi_time_part77_atomic_centered_residue_tight_frame (m : Nat) (hm : 2 ≤ m) :
    IsRegularSimplexFamily (atomicCenteredResidueVector m) ∧
      ∀ v : Fin m → ℤ, (∑ r, v r = 0) →
        ∑ ℓ, atomicCenteredResidueInner v (atomicCenteredResidueVector m ℓ) ^ (2 : Nat) =
          (4 : ℤ) * (m : ℤ) ^ (2 : Nat) * atomicCenteredResidueInner v v := by
  exact
    ⟨paper_xi_time_part65c_atomic_centered_residue_simplex m hm,
      fun v hv => paper_xi_time_part65c_atomic_centered_residue_isotropic m hm v hv⟩

end Omega.Zeta
