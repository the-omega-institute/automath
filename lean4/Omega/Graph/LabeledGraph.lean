import Omega.Core.Word

namespace Omega.Graph

universe u v

/-- A finite-word labeled graph viewed as a step relation.
    def:golden-mean-labeled-graph -/
structure LabeledGraph (σ : Type u) (α : Type v) where
  edge : σ → α → σ → Prop

/-- The state index before reading coordinate `i`. -/
def before (i : Fin m) : Fin (m + 1) :=
  ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self m)⟩

/-- The state index after reading coordinate `i`. -/
def after (i : Fin m) : Fin (m + 1) :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

@[simp] theorem before_val (i : Fin m) : (before i).1 = i.1 := rfl

@[simp] theorem after_val (i : Fin m) : (after i).1 = i.1 + 1 := rfl

/-- A labeled graph accepts a finite sequence when there is a compatible state path. -/
def AcceptsSeq (G : LabeledGraph σ α) (start : σ) (u : Fin m → α) : Prop :=
  ∃ qs : Fin (m + 1) → σ,
    qs ⟨0, Nat.succ_pos m⟩ = start ∧
    ∀ i : Fin m, G.edge (qs (before i)) (u i) (qs (after i))

/-- Binary-word specialization of `AcceptsSeq`. -/
abbrev AcceptsWord (G : LabeledGraph σ Bool) (start : σ) (w : Word m) : Prop :=
  AcceptsSeq G start w

end Omega.Graph
