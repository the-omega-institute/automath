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

/-- The `+`-eigenspace is indexed by three Walsh families over the residual
`m - 2` coordinates. -/
abbrev window6WalshPlusIndex (m : Nat) := Fin 3 × Omega.Word (m - 2)

/-- The `-`-eigenspace is indexed by one Walsh family over the residual
`m - 2` coordinates. -/
abbrev window6WalshMinusIndex (m : Nat) := Omega.Word (m - 2)

/-- Cardinality of the modeled `+`-eigenbasis. -/
def window6WalshPlusBasisCardinality (m : Nat) : Nat :=
  Fintype.card (window6WalshPlusIndex m)

/-- Cardinality of the modeled `-`-eigenbasis. -/
def window6WalshMinusBasisCardinality (m : Nat) : Nat :=
  Fintype.card (window6WalshMinusIndex m)

/-- Count form of the Walsh direct-sum decomposition for the window-6 affine
chiral involution.
    thm:window6-affine-chiral-walsh-decomposition -/
theorem paper_window6_affine_chiral_walsh_decomposition (m : Nat) (hm : 2 ≤ m) :
    window6WalshPlusBasisCardinality m = 3 * 2 ^ (m - 2) ∧
      window6WalshMinusBasisCardinality m = 2 ^ (m - 2) ∧
      window6WalshPlusBasisCardinality m + window6WalshMinusBasisCardinality m =
        Fintype.card (Omega.Word m) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [window6WalshPlusBasisCardinality, window6WalshPlusIndex, Omega.Word]
  · simp [window6WalshMinusBasisCardinality, window6WalshMinusIndex, Omega.Word]
  · have hplus : window6WalshPlusBasisCardinality m = 3 * 2 ^ (m - 2) := by
      simp [window6WalshPlusBasisCardinality, window6WalshPlusIndex, Omega.Word]
    have hminus : window6WalshMinusBasisCardinality m = 2 ^ (m - 2) := by
      simp [window6WalshMinusBasisCardinality, window6WalshMinusIndex, Omega.Word]
    have hm' : m = (m - 2) + 2 := by omega
    calc
      window6WalshPlusBasisCardinality m + window6WalshMinusBasisCardinality m
          = 3 * 2 ^ (m - 2) + 2 ^ (m - 2) := by rw [hplus, hminus]
      _ = 4 * 2 ^ (m - 2) := by ring
      _ = 2 ^ ((m - 2) + 2) := by
            simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              (Nat.pow_add 2 (m - 2) 2).symm
      _ = Fintype.card (Omega.Word m) := by
            rw [hm']
            simp [Omega.Word]

end Omega.GU
