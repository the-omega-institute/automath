import Mathlib.Tactic
import Omega.SPG.DyadicCubicalBoundaryInjective

namespace Omega.SPG

/-- Paper wrapper for dyadic boundary syndrome fillability:
    local syndrome closure is equivalent to being a top boundary, and injectivity
    of the top boundary map gives uniqueness of the filling.
    cor:spg-dyadic-boundary-syndrome-fillability -/
theorem paper_spg_dyadic_boundary_syndrome_fillability
    {Cn Cn1 Cn2 Syndrome : Type*}
    [AddGroup Cn] [AddGroup Cn1] [AddGroup Cn2] [AddGroup Syndrome]
    (boundaryTop : Cn → Cn1)
    (boundaryLower : Cn1 → Cn2)
    (syndrome : Cn1 → Syndrome)
    (hSyndrome : ∀ b, syndrome b = 0 ↔ boundaryLower b = 0)
    (hChain : ∀ x, boundaryLower (boundaryTop x) = 0)
    (hExact : ∀ b, boundaryLower b = 0 → ∃ x, boundaryTop x = b)
    (hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v)
    (hKer : ∀ u, boundaryTop u = 0 → u = 0)
    (b : Cn1) :
    ((∃ x, boundaryTop x = b) ↔ syndrome b = 0) ∧
    (syndrome b = 0 → ∃! x, boundaryTop x = b) := by
  have hInj : Function.Injective boundaryTop :=
    paper_spg_dyadic_cubical_boundary_injective boundaryTop hSub hKer
  refine ⟨?_, ?_⟩
  · constructor
    · intro hb
      rcases hb with ⟨x, rfl⟩
      exact (hSyndrome _).2 (hChain x)
    · intro hb
      exact hExact b ((hSyndrome b).1 hb)
  · intro hb
    rcases hExact b ((hSyndrome b).1 hb) with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact hInj (hy.trans hx.symm)

end Omega.SPG
