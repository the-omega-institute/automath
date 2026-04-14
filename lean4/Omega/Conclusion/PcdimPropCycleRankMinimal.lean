import Omega.Conclusion.BoundaryCycleRankExternalInfoLowerBound
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: an `F_p`-linear embedding of an `r`-dimensional cycle space into the
mod-`p` quotient `K/pK` forces `r ≤ pcdim(K)`, and the standard rank-`r` model `Z_p^r` attains
this lower bound via the identity embedding.
    cor:conclusion-pcdim-prop-cycle-rank-minimal -/
theorem paper_conclusion_pcdim_prop_cycle_rank_minimal
    (p r : ℕ) [Fact p.Prime]
    {Kmod : Type} [AddCommGroup Kmod] [Module (ZMod p) Kmod]
    [FiniteDimensional (ZMod p) Kmod]
    (inject : (Fin r → ZMod p) →ₗ[ZMod p] Kmod)
    (hinj : Function.Injective inject) :
    r ≤ Module.finrank (ZMod p) Kmod ∧
      Module.finrank (ZMod p) (Fin r → ZMod p) = r ∧
      ∃ witness : (Fin r → ZMod p) →ₗ[ZMod p] (Fin r → ZMod p),
        Function.Injective witness := by
  refine ⟨?_, Module.finrank_fin_fun (R := ZMod p), ?_⟩
  · simpa [Module.finrank_fin_fun (R := ZMod p)] using
      (LinearMap.finrank_le_finrank_of_injective hinj)
  · exact ⟨LinearMap.id, fun _ _ h => h⟩

end Omega.Conclusion
