import Mathlib.Tactic
import Omega.SPG.DyadicCubicalBoundaryInjective

namespace Omega.SPG

/-- A fundamental-cycle obstruction recording the inspected cycle and its signed edge sum. -/
structure IntegerCycleCertificate (Edge : Type*) where
  cycleEdges : List Edge
  signedSum : ℤ

/-- Paper wrapper for integer-valued bulk decoding on the adjacency graph:
    either tree propagation returns a filling whose boundary matches the input,
    or a fundamental cycle carries a nonzero signed edge sum and certifies
    inconsistency. Injectivity of the boundary map gives uniqueness in the
    fillable case.
    thm:spg-integer-bulk-decode-or-cycle-certificate -/
theorem paper_spg_integer_bulk_decode_or_cycle_certificate :
    ∀ {Cn Cn1 Edge : Type*} [AddGroup Cn] [AddGroup Cn1]
      (boundary : Cn → Cn1)
      (decodeFromBoundary : Cn1 → Cn)
      (cycleCert : Cn1 → IntegerCycleCertificate Edge)
      (work : Cn1 → Nat) (vertexCount edgeCount : Nat)
      (_hDecodeOrCycle :
        ∀ b, boundary (decodeFromBoundary b) = b ∨ (cycleCert b).signedSum ≠ 0)
      (_hCycleObstructs :
        ∀ b, (cycleCert b).signedSum ≠ 0 → ∀ x, boundary x ≠ b)
      (_hBoundarySub : ∀ u v, boundary (u - v) = boundary u - boundary v)
      (_hBoundaryKer : ∀ u, boundary u = 0 → u = 0)
      (_hLinear : ∀ b, work b ≤ vertexCount + edgeCount),
      (∀ b, work b ≤ vertexCount + edgeCount) ∧
      (∀ b, (∃! x, boundary x = b) ∨
        ∃ γ : IntegerCycleCertificate Edge,
          γ = cycleCert b ∧ γ.signedSum ≠ 0 ∧ ∀ x, boundary x ≠ b) := by
  intro Cn Cn1 Edge _ _ boundary decodeFromBoundary cycleCert work vertexCount edgeCount
    hDecodeOrCycle hCycleObstructs hBoundarySub hBoundaryKer hLinear
  refine ⟨hLinear, ?_⟩
  intro b
  have hInj : Function.Injective boundary :=
    paper_spg_dyadic_cubical_boundary_injective boundary hBoundarySub hBoundaryKer
  rcases hDecodeOrCycle b with hDecode | hCycle
  · left
    refine ⟨decodeFromBoundary b, hDecode, ?_⟩
    intro y hy
    exact hInj (hy.trans hDecode.symm)
  · right
    refine ⟨cycleCert b, rfl, hCycle, ?_⟩
    exact hCycleObstructs b hCycle

end Omega.SPG
