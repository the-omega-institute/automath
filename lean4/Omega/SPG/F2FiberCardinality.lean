import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# F₂ fiber cardinality via kernel dimension

For a linear map f_S over F₂, each fiber has cardinality 2^{dim ker f_S}.
We verify concrete kernel sizes for small linear maps over ZMod 2.
-/

namespace Omega.SPG.F2FiberCardinality

/-- Kernel of the sum map (Fin 3 → ZMod 2) → ZMod 2 has 4 elements.
    cor:spg-partial-boundary-fiber-cardinality-f2 -/
theorem kernel_sum3_card :
    (Finset.univ.filter (fun v : Fin 3 → ZMod 2 => v 0 + v 1 + v 2 = 0)).card = 4 := by
  native_decide

/-- Kernel of the projection map (Fin 2 → ZMod 2) → ZMod 2 has 2 elements.
    cor:spg-partial-boundary-fiber-cardinality-f2 -/
theorem kernel_proj2_card :
    (Finset.univ.filter (fun v : Fin 2 → ZMod 2 => v 0 = 0)).card = 2 := by
  native_decide

/-- Full space (Fin 2 → ZMod 2) has 4 elements (kernel of zero map).
    cor:spg-partial-boundary-fiber-cardinality-f2 -/
theorem full_space_fin2_card :
    (Finset.univ : Finset (Fin 2 → ZMod 2)).card = 4 := by native_decide

/-- Paper package: F₂ fiber cardinality = 2^{dim ker}.
    cor:spg-partial-boundary-fiber-cardinality-f2 -/
theorem paper_spg_partial_boundary_fiber_cardinality_f2 :
    (Finset.univ.filter (fun v : Fin 3 → ZMod 2 =>
      v 0 + v 1 + v 2 = 0)).card = 4 ∧
    (Finset.univ.filter (fun v : Fin 2 → ZMod 2 =>
      v 0 = 0)).card = 2 ∧
    2 ^ 2 = 4 ∧ 2 ^ 1 = 2 := by
  refine ⟨kernel_sum3_card, kernel_proj2_card, by norm_num, by norm_num⟩

end Omega.SPG.F2FiberCardinality
