import Omega.Folding.FoldZeroHalfIndexMultiple6
import Omega.Zeta.XiBinfoldRenyi2EntropyDefectConstant

namespace Omega.Zeta

open Omega.Folding
open XiBinfoldRenyi2EntropyDefectConstantData

/-- Paper label: `cor:xi-binfold-zero-block-collision-gap-decoupling`.
The visible half-index zero block gives the absolute lower bound, the sparse-density estimate gives
the relative upper bound, and the already formalized Rényi-`2` theorem supplies the collision-gap
lower bound. -/
theorem paper_xi_binfold_zero_block_collision_gap_decoupling
    (D : XiBinfoldRenyi2EntropyDefectConstantData) (hm : (D.m + 2) % 6 = 0)
    (hM : Even (Nat.fib (D.m + 2))) :
    Nat.fib ((D.m + 2) / 2) ≤ (foldZeroFrequencyUnion D.m).card ∧
      (((foldZeroFrequencyUnion D.m).card : ℚ) / Nat.fib (D.m + 2) ≤
        ((((D.m + 2).divisors.card * Nat.fib ((D.m + 2) / 2) : ℕ) : ℚ) / Nat.fib (D.m + 2))) ∧
      XiBinfoldRenyi2EntropyDefectConstantData.natLowerBound D := by
  have hhalf := (paper_fold_zero_half_index_multiple6 D.m hm).2
  have hsparse := (paper_fold_zero_density_sparse D.m hM).2
  have hgap := (paper_xi_binfold_renyi2_entropy_defect_constant D).1
  exact ⟨hhalf, hsparse, hgap⟩

end Omega.Zeta
