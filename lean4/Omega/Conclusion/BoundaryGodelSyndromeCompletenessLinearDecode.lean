import Mathlib.Tactic
import Omega.SPG.DyadicBoundarySyndromeFillability
import Omega.SPG.LinearTimeBulkDecodeFromBoundary

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-godel-syndrome-completeness-linear-decode`. The
dyadic-boundary syndrome criterion identifies the admissible boundary codes, and the rooted-tree
bulk decoder upgrades admissibility to unique fillability with linear-time work. -/
theorem paper_conclusion_boundary_godel_syndrome_completeness_linear_decode
    {Cn Cn1 Cn2 Syndrome : Type*}
    [AddGroup Cn] [AddGroup Cn1] [AddGroup Cn2] [AddGroup Syndrome]
    (boundaryTop : Cn → Cn1)
    (boundaryLower : Cn1 → Cn2)
    (syndrome : Cn1 → Syndrome)
    (decodeFromBoundary : Cn1 → Cn)
    (work : Cn1 → Nat) (vertexCount edgeCount : Nat)
    (hSyndrome : ∀ b, syndrome b = 0 ↔ boundaryLower b = 0)
    (hChain : ∀ x, boundaryLower (boundaryTop x) = 0)
    (hExact : ∀ b, boundaryLower b = 0 → ∃ x, boundaryTop x = b)
    (hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v)
    (hKer : ∀ u, boundaryTop u = 0 → u = 0)
    (hDecode : ∀ b, boundaryTop (decodeFromBoundary b) = b)
    (hLinear : ∀ b, work b ≤ vertexCount + edgeCount)
    (b : Cn1) :
    ((∃ x, boundaryTop x = b) ↔ syndrome b = 0) ∧
      (syndrome b = 0 → ∃! x, boundaryTop x = b ∧ work b ≤ vertexCount + edgeCount) := by
  rcases Omega.SPG.paper_spg_dyadic_boundary_syndrome_fillability
      boundaryTop boundaryLower syndrome hSyndrome hChain hExact hSub hKer b with
    ⟨hiff, hfillUnique⟩
  have hdecodePkg := Omega.SPG.paper_spg_linear_time_bulk_decode_from_boundary_proof
      boundaryTop decodeFromBoundary work vertexCount edgeCount hDecode hSub hKer hLinear
  refine ⟨hiff, ?_⟩
  intro hb
  have hwork : work b ≤ vertexCount + edgeCount := hdecodePkg.1 b
  rcases hdecodePkg.2 b with ⟨x, hx, hxuniq⟩
  refine ⟨x, ⟨hx, hwork⟩, ?_⟩
  intro y hy
  exact hxuniq y hy.1

end Omega.Conclusion
