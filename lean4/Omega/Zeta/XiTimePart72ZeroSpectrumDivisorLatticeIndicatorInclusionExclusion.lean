import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

attribute [local instance] Classical.propDecidable

/-- Paper label:
`thm:xi-time-part72-zero-spectrum-divisor-lattice-indicator-inclusion-exclusion`.
The clique-based inclusion-exclusion formula can be rewritten termwise using the compatible
indicator on the same nonempty divisor-lattice powerset. -/
theorem paper_xi_time_part72_zero_spectrum_divisor_lattice_indicator_inclusion_exclusion
    (D : Finset ℕ) (clique compatible : Finset ℕ -> Prop) (gcdWeight : Finset ℕ -> ℤ) (zCard : ℤ)
    (hClique : zCard = Finset.sum (D.powerset.filter (fun I => I.Nonempty)) (fun I =>
      if clique I then (-1 : ℤ) ^ (I.card + 1) * gcdWeight I else 0))
    (hCompat : ∀ I, I ⊆ D -> (clique I ↔ compatible I)) :
    zCard = Finset.sum (D.powerset.filter (fun I => I.Nonempty)) (fun I =>
      if compatible I then (-1 : ℤ) ^ (I.card + 1) * gcdWeight I else 0) := by
  calc
    zCard = Finset.sum (D.powerset.filter (fun I => I.Nonempty)) (fun I =>
        if clique I then (-1 : ℤ) ^ (I.card + 1) * gcdWeight I else 0) := hClique
    _ = Finset.sum (D.powerset.filter (fun I => I.Nonempty)) (fun I =>
        if compatible I then (-1 : ℤ) ^ (I.card + 1) * gcdWeight I else 0) := by
          refine Finset.sum_congr rfl ?_
          intro I hI
          have hsubset : I ⊆ D := by
            exact Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
          simp [hCompat I hsubset]

end Omega.Zeta
