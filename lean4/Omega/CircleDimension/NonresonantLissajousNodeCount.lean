import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A finite ledger for the two reflection families of nodes on a nonresonant Lissajous orbit.
The ambient node type is abstract: the arithmetic geometry work establishing injectivity,
disjointness, and transversality is recorded in the witness, while this file packages the final
count. -/
structure NonresonantLissajousNodeLedger (a b : ℕ) where
  Node : Type
  instFintypeNode : Fintype Node
  nodePosNeg : Fin (a - 1) × Fin b → Node
  nodeNegPos : Fin a × Fin (b - 1) → Node
  transverse : Node → Prop
  posNeg_injective : Function.Injective nodePosNeg
  negPos_injective : Function.Injective nodeNegPos
  families_disjoint : ∀ u v, nodePosNeg u ≠ nodeNegPos v
  cover : ∀ x : Node, (∃ u, nodePosNeg u = x) ∨ ∃ v, nodeNegPos v = x
  transverse_posNeg : ∀ u, transverse (nodePosNeg u)
  transverse_negPos : ∀ v, transverse (nodeNegPos v)

attribute [instance] NonresonantLissajousNodeLedger.instFintypeNode

set_option maxHeartbeats 400000 in
/-- Paper-facing node count for a nonresonant coprime Lissajous orbit: once the two reflection
families are known to be injective, disjoint, exhaustive, and transverse, the total number of
nodes is the sum of the two reflection-family counts, and every node is transverse.
    thm:cdim-nonresonant-lissajous-node-count -/
theorem paper_cdim_nonresonant_lissajous_node_count
    {a b : ℕ} (_ha : 1 ≤ a) (_hb : 1 ≤ b) (L : NonresonantLissajousNodeLedger a b) :
    Fintype.card L.Node = (a - 1) * b + a * (b - 1) ∧ ∀ x : L.Node, L.transverse x := by
  let f : (Fin (a - 1) × Fin b) ⊕ (Fin a × Fin (b - 1)) → L.Node :=
    Sum.elim L.nodePosNeg L.nodeNegPos
  have hf_inj : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y
    · simp only [f] at hxy
      exact congrArg Sum.inl (L.posNeg_injective hxy)
    · simp only [f] at hxy
      exact (L.families_disjoint _ _ hxy).elim
    · simp only [f] at hxy
      exact (L.families_disjoint _ _ hxy.symm).elim
    · simp only [f] at hxy
      exact congrArg Sum.inr (L.negPos_injective hxy)
  have hf_surj : Function.Surjective f := by
    intro x
    rcases L.cover x with h | h
    · rcases h with ⟨u, rfl⟩
      exact ⟨Sum.inl u, rfl⟩
    · rcases h with ⟨v, rfl⟩
      exact ⟨Sum.inr v, rfl⟩
  have hcard :
      Fintype.card L.Node =
        Fintype.card ((Fin (a - 1) × Fin b) ⊕ (Fin a × Fin (b - 1))) := by
    symm
    exact Fintype.card_of_bijective (f := f) ⟨hf_inj, hf_surj⟩
  have hcount :
      Fintype.card L.Node = (a - 1) * b + a * (b - 1) := by
    rw [hcard, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    simp
  refine ⟨hcount, ?_⟩
  intro x
  rcases L.cover x with h | h
  · rcases h with ⟨u, rfl⟩
    exact L.transverse_posNeg u
  · rcases h with ⟨v, rfl⟩
    exact L.transverse_negPos v

end Omega.CircleDimension
