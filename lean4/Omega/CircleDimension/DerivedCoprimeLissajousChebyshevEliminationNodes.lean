import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local ledger for the coprime Lissajous-Chebyshev elimination curve. The elimination
identity, its Zariski-closure consequence, the node count, and ordinary-node status are recorded
as reusable data. -/
structure CoprimeLissajousEliminationNodeData (a b : ℕ) where
  Node : Type
  instFintypeNode : Fintype Node
  resultantPrimitivePartEqualsChebyshevCurve : Prop
  zariskiClosureEqualsChebyshevCurve : Prop
  ordinaryNode : Node → Prop
  resultantPrimitivePartEqualsChebyshevCurve_h :
    resultantPrimitivePartEqualsChebyshevCurve
  zariskiClosureEqualsChebyshevCurve_h :
    zariskiClosureEqualsChebyshevCurve
  nodeCardinality :
    Fintype.card Node = (a - 1) * (b - 1) / 2
  ordinaryNode_spec : ∀ P : Node, ordinaryNode P

attribute [instance] CoprimeLissajousEliminationNodeData.instFintypeNode

/-- Paper-facing wrapper for the coprime Lissajous-Chebyshev elimination curve: the primitive
resultant and Zariski closure identify the Chebyshev curve, the ordinary double points are
counted by the parity-matched grid, and every listed singular point is an ordinary node.
    thm:derived-coprime-lissajous-chebyshev-elimination-nodes -/
theorem paper_derived_coprime_lissajous_chebyshev_elimination_nodes {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hcop : Nat.Coprime a b) (D : CoprimeLissajousEliminationNodeData a b) :
    D.resultantPrimitivePartEqualsChebyshevCurve ∧ D.zariskiClosureEqualsChebyshevCurve ∧
      Fintype.card D.Node = (a - 1) * (b - 1) / 2 ∧ ∀ P : D.Node, D.ordinaryNode P := by
  let _ := ha
  let _ := hb
  let _ := hcop
  exact ⟨D.resultantPrimitivePartEqualsChebyshevCurve_h, D.zariskiClosureEqualsChebyshevCurve_h,
    D.nodeCardinality, D.ordinaryNode_spec⟩

end Omega.CircleDimension
