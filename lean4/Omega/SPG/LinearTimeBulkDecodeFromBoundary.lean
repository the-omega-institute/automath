import Mathlib.Tactic
import Omega.SPG.DyadicCubicalBoundaryInjective

namespace Omega.SPG

/-- Paper wrapper for rooted-tree bulk decoding from boundary data:
    a tree propagation routine with cycle-consistent edge labels reconstructs a
    filling in linear work, and injectivity of the top boundary map makes that
    filling unique.
    thm:spg-linear-time-bulk-decode-from-boundary -/
def paper_spg_linear_time_bulk_decode_from_boundary : Prop :=
  ∀ {Cn Cn1 : Type*} [AddGroup Cn] [AddGroup Cn1]
    (boundary : Cn → Cn1)
    (decodeFromBoundary : Cn1 → Cn)
    (work : Cn1 → Nat) (vertexCount edgeCount : Nat)
    (_hTreePropagation : ∀ b, boundary (decodeFromBoundary b) = b)
    (_hCycleConsistent : ∀ u v, boundary (u - v) = boundary u - boundary v)
    (_hKernel : ∀ u, boundary u = 0 → u = 0)
    (_hLinear : ∀ b, work b ≤ vertexCount + edgeCount),
    (∀ b, work b ≤ vertexCount + edgeCount) ∧
    (∀ b, ∃! x, boundary x = b)

theorem paper_spg_linear_time_bulk_decode_from_boundary_proof :
    paper_spg_linear_time_bulk_decode_from_boundary := by
  intro Cn Cn1 _ _ boundary decodeFromBoundary work vertexCount edgeCount
    hTreePropagation hCycleConsistent hKernel hLinear
  refine ⟨hLinear, ?_⟩
  intro b
  refine ⟨decodeFromBoundary b, hTreePropagation b, ?_⟩
  intro y hy
  have hInj : Function.Injective boundary :=
    paper_spg_dyadic_cubical_boundary_injective boundary hCycleConsistent hKernel
  exact hInj (hy.trans (hTreePropagation b).symm)

end Omega.SPG
