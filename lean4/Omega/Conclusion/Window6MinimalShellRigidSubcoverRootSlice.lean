import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The eight `X₄` states whose `01`-suffix lift forms the rigid minimal shell in `X₆`. -/
inductive Window4RigidTail
  | b1000
  | b1001
  | b1010
  | b0000
  | b0100
  | b0010
  | b0001
  | b0101
  deriving DecidableEq, Fintype

/-- The explicit suffix embedding `ι₄(x) = x01` into the window-6 shell. -/
def window6SuffixEmbedding : Window4RigidTail → Fin 64
  | .b1000 => ⟨33, by decide⟩
  | .b1001 => ⟨37, by decide⟩
  | .b1010 => ⟨41, by decide⟩
  | .b0000 => ⟨1, by decide⟩
  | .b0100 => ⟨17, by decide⟩
  | .b0010 => ⟨9, by decide⟩
  | .b0001 => ⟨5, by decide⟩
  | .b0101 => ⟨21, by decide⟩

def w100001 : Fin 64 := ⟨33, by decide⟩
def w100101 : Fin 64 := ⟨37, by decide⟩
def w101001 : Fin 64 := ⟨41, by decide⟩
def w000001 : Fin 64 := ⟨1, by decide⟩
def w010001 : Fin 64 := ⟨17, by decide⟩
def w001001 : Fin 64 := ⟨9, by decide⟩
def w000101 : Fin 64 := ⟨5, by decide⟩
def w010101 : Fin 64 := ⟨21, by decide⟩

/-- The minimal shell `S_{6,2}`. -/
def window6MinimalShell : Finset (Fin 64) :=
  Finset.univ.image window6SuffixEmbedding

/-- The three boundary fibers inside the minimal shell. -/
def window6BoundaryFiber : Finset (Fin 64) :=
  {w100001, w100101, w101001}

/-- The five cyclic fibers inside the minimal shell. -/
def window6CyclicFiber : Finset (Fin 64) :=
  {w000001, w010001, w001001, w000101, w010101}

/-- The five cyclic generators are packaged as a `B₃` root slice. -/
abbrev Window6B3RootSlice := Fin 5

/-- The three visible boundary generators. -/
abbrev Window6BoundaryGenerators := Fin 3

/-- The center decomposition is the direct sum of the cyclic and boundary generators. -/
abbrev Window6CenterGenerators := Window6B3RootSlice ⊕ Window6BoundaryGenerators

/-- The minimal shell is exactly the `01`-suffix suspension of the chosen `X₄` subcover. -/
theorem window6_minimal_step_suffix_suspension :
    window6MinimalShell =
      {w100001, w100101, w101001, w000001, w010001, w001001, w000101, w010101} := by
  decide

/-- The boundary and cyclic pieces are disjoint and cover the rigid minimal shell. -/
theorem window6_minimal_shell_decomposition :
    Disjoint window6BoundaryFiber window6CyclicFiber ∧
      window6BoundaryFiber ∪ window6CyclicFiber = window6MinimalShell := by
  refine ⟨by decide, ?_⟩
  rw [window6_minimal_step_suffix_suspension]
  decide

/-- Paper-facing wrapper for the window-6 rigid subcover: the `01`-suffix embedding produces the
eight-point shell, the shell splits into three boundary fibers and five cyclic fibers, and the
resulting center decomposition has `5 + 3 = 8` generators.
    thm:conclusion-window6-minimal-shell-rigid-subcover-root-slice -/
theorem paper_conclusion_window6_minimal_shell_rigid_subcover_root_slice :
    window6MinimalShell = Finset.univ.image window6SuffixEmbedding ∧
      window6BoundaryFiber = {w100001, w100101, w101001} ∧
      window6CyclicFiber = {w000001, w010001, w001001, w000101, w010101} ∧
      window6BoundaryFiber.card = 3 ∧
      window6CyclicFiber.card = 5 ∧
      Fintype.card Window6CenterGenerators =
        Fintype.card Window6B3RootSlice + Fintype.card Window6BoundaryGenerators := by
  refine ⟨rfl, rfl, rfl, by decide, by decide, ?_⟩
  decide

end Omega.Conclusion
