import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

namespace FiniteDimensional

/-- Compatibility alias for the `finrank` API used by paper-facing theorem statements. -/
noncomputable abbrev finrank (K : Type*) (V : Type*) [Semiring K] [AddCommMonoid V] [Module K V] :
    ℕ :=
  Module.finrank K V

end FiniteDimensional

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- If the center `2`-torsion has `F₂`-dimension at most `1`, then it cannot contain an injective
copy of `(Z/2)^3`.
    cor:foldbin-center-2torsion-dimension-obstruction-m2 -/
theorem paper_foldbin_center_2torsion_dimension_obstruction_m2
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hV : FiniteDimensional.finrank (ZMod 2) V ≤ 1) :
    ¬ ∃ f : (Fin 3 → ZMod 2) →ₗ[ZMod 2] V, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hdim : 3 ≤ FiniteDimensional.finrank (ZMod 2) V := by
    simpa [Module.finrank_fin_fun (R := ZMod 2)] using
      (LinearMap.finrank_le_finrank_of_injective hf :
        FiniteDimensional.finrank (ZMod 2) (Fin 3 → ZMod 2) ≤
          FiniteDimensional.finrank (ZMod 2) V)
  omega

end Omega.GroupUnification
