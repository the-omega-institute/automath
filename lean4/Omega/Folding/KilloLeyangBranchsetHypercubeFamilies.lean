import Omega.CircleDimension.DyadicKernelCube
import Omega.Folding.KilloLeyang2powerTorsionCayleyHypercube

namespace Omega.Folding

/-- Paper label: `prop:killo-leyang-branchset-hypercube-families`.
Each dyadic branch component carries the explicit `2n`-hypercube address coming from the
`(ZMod (2^n))²` torsion model, and the finite-level truncations are the dyadic kernel-cube
equivalences already formalized in the circle-dimension chapter. -/
theorem paper_killo_leyang_branchset_hypercube_families (n : ℕ) :
    Nonempty ((ZMod (2 ^ n) × ZMod (2 ^ n)) ≃ Omega.Word (2 * n)) ∧
      Nonempty (ZMod (2 ^ n) ≃ (Fin n → Bool)) ∧
      Nonempty (((Fin 6) → ZMod (2 ^ n)) ≃ (Fin (6 * n) → Bool)) := by
  rcases Omega.CircleDimension.paper_cdim_dyadic_kernel_cube_inverse_limit n with ⟨hstage, hsix⟩
  refine ⟨?_, hstage, hsix⟩
  exact ⟨(Equiv.ofBijective
    (killo_leyang_2power_torsion_cayley_hypercube_address n)
    (paper_killo_leyang_2power_torsion_cayley_hypercube n)).symm⟩

end Omega.Folding
