import Mathlib.Tactic
import Omega.Folding.HammingDist

namespace Omega.GU

/-- Attach the equal boundary pair `bb` to a tail word. -/
def chiralBoundaryLift (b : Bool) (t : Omega.Word n) : Omega.Word (n + 2) :=
  Omega.snoc (Omega.snoc t b) b

/-- Forget the two distinguished boundary coordinates. -/
def chiralBoundaryTail (w : Omega.Word (n + 2)) : Omega.Word n :=
  Omega.truncate (Omega.truncate w)

/-- Swap the two distinguished coordinates and complement both bits. -/
def chiralBoundaryInvolution (w : Omega.Word (n + 2)) : Omega.Word (n + 2) :=
  Omega.snoc (Omega.snoc (chiralBoundaryTail w) (!Omega.last w)) (!Omega.last (Omega.truncate w))

@[simp] theorem chiralBoundaryTail_lift (b : Bool) (t : Omega.Word n) :
    chiralBoundaryTail (chiralBoundaryLift b t) = t := by
  simp [chiralBoundaryTail, chiralBoundaryLift]

@[simp] theorem chiralBoundaryInvolution_lift (b : Bool) (t : Omega.Word n) :
    chiralBoundaryInvolution (chiralBoundaryLift b t) = chiralBoundaryLift (!b) t := by
  cases b <;> simp [chiralBoundaryInvolution, chiralBoundaryLift, chiralBoundaryTail]

@[simp] theorem hammingDist_chiralBoundaryLift (b : Bool) (u v : Omega.Word n) :
    Omega.hammingDist (chiralBoundaryLift b u) (chiralBoundaryLift b v) = Omega.hammingDist u v := by
  cases b <;> simp [chiralBoundaryLift, Omega.hammingDist_snoc]

/-- Paper-facing statement: the anti-invariant `00/11` boundary pair over a tail word is exchanged
    by the affine involution, and the hypercube Hamming metric on those paired lifts is exactly the
    metric on the tail cube. -/
def paper_window6_chiral_compression_hypercube_adjacency_stmt (m : Nat) : Prop :=
  let n := m - 2
  (∀ t : Omega.Word n,
    chiralBoundaryTail (chiralBoundaryLift false t) = t ∧
      chiralBoundaryTail (chiralBoundaryLift true t) = t ∧
      chiralBoundaryInvolution (chiralBoundaryLift false t) = chiralBoundaryLift true t ∧
      chiralBoundaryInvolution (chiralBoundaryLift true t) = chiralBoundaryLift false t) ∧
    (∀ u v : Omega.Word n,
      Omega.hammingDist (chiralBoundaryLift false u) (chiralBoundaryLift false v) =
        Omega.hammingDist u v) ∧
    (∀ u v : Omega.Word n,
      Omega.hammingDist (chiralBoundaryLift true u) (chiralBoundaryLift true v) =
        Omega.hammingDist u v)

theorem paper_window6_chiral_compression_hypercube_adjacency (m : Nat) (hm : 2 <= m) :
    paper_window6_chiral_compression_hypercube_adjacency_stmt m := by
  let _ := hm
  let n := m - 2
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact ⟨chiralBoundaryTail_lift false t, chiralBoundaryTail_lift true t,
      chiralBoundaryInvolution_lift false t, chiralBoundaryInvolution_lift true t⟩
  · intro u v
    exact hammingDist_chiralBoundaryLift false u v
  · intro u v
    exact hammingDist_chiralBoundaryLift true u v

end Omega.GU
