import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-dyadic-boundary-fillability-construction-split`. Local syndrome
vanishing is equivalent to boundary fillability, while the supplied decoder gives the unique
linear-work filling. -/
theorem paper_conclusion_dyadic_boundary_fillability_construction_split
    {Cn Cn1 Cn2 Syndrome : Type*}
    [AddGroup Cn] [AddGroup Cn1] [AddGroup Cn2] [AddGroup Syndrome]
    (boundaryTop : Cn → Cn1)
    (boundaryLower : Cn1 → Cn2)
    (syndrome : Cn1 → Syndrome)
    (decodeFromBoundary : Cn1 → Cn)
    (work : Cn1 → Nat)
    (vertexCount edgeCount : Nat)
    (hSyndrome : ∀ b, syndrome b = 0 ↔ boundaryLower b = 0)
    (hChain : ∀ x, boundaryLower (boundaryTop x) = 0)
    (hExact : ∀ b, boundaryLower b = 0 → ∃ x, boundaryTop x = b)
    (hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v)
    (hKer : ∀ u, boundaryTop u = 0 → u = 0)
    (hDecode : ∀ b, boundaryTop (decodeFromBoundary b) = b)
    (hLinear : ∀ b, work b ≤ vertexCount + edgeCount) :
    ∀ b, ((∃ x, boundaryTop x = b) ↔ syndrome b = 0) ∧
      (syndrome b = 0 →
        ∃! x, boundaryTop x = b ∧ work b ≤ vertexCount + edgeCount) := by
  intro b
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨x, rfl⟩
      exact (hSyndrome (boundaryTop x)).2 (hChain x)
    · intro hb
      exact hExact b ((hSyndrome b).1 hb)
  · intro _hb
    refine ⟨decodeFromBoundary b, ⟨hDecode b, hLinear b⟩, ?_⟩
    intro y hy
    have hboundarySub : boundaryTop (y - decodeFromBoundary b) = 0 := by
      rw [hSub, hy.1, hDecode b, sub_self]
    exact sub_eq_zero.mp (hKer (y - decodeFromBoundary b) hboundarySub)

end Omega.Conclusion
