import Omega.Folding.HammingDist

/-! ### Fibonacci Cube Graph

The Fibonacci cube Γ_n is a graph whose vertices are length-n binary words
with no adjacent 1s (i.e., elements of X_n). Two vertices are adjacent iff they
differ in exactly one position (Hamming distance 1), and the flipped word is
still a valid No11 word. This file defines the adjacency relation and proves
basic structural properties. -/

namespace Omega.Combinatorics.FibonacciCubeGraph

open Omega

/-- Fibonacci cube adjacency: two No11 words of length m are adjacent iff they
    differ in exactly one coordinate (Hamming distance 1).
    Note: since both endpoints are No11, the constraint "flipped word still legal"
    is automatically satisfied — it is part of the X m type.
    def:pom-fibonacci-cube -/
def fibCubeAdj {m : Nat} (x y : X m) : Prop :=
  x ≠ y ∧ hammingDist x.1 y.1 = 1

/-- Fibonacci cube adjacency is irreflexive.
    def:pom-fibonacci-cube -/
theorem fibCubeAdj_irrefl {m : Nat} (x : X m) : ¬fibCubeAdj x x := by
  intro ⟨hne, _⟩
  exact hne rfl

/-- Fibonacci cube adjacency is symmetric.
    def:pom-fibonacci-cube -/
theorem fibCubeAdj_symm {m : Nat} (x y : X m) :
    fibCubeAdj x y → fibCubeAdj y x := by
  intro ⟨hne, hd⟩
  exact ⟨hne ∘ Eq.symm, by rw [hammingDist_comm]; exact hd⟩

/-- Adjacent vertices differ in at most one position (tautology from definition).
    def:pom-fibonacci-cube -/
theorem fibCubeAdj_hamming_one {m : Nat} {x y : X m}
    (h : fibCubeAdj x y) : hammingDist x.1 y.1 = 1 :=
  h.2

/-- Two distinct vertices with Hamming distance 1 are adjacent.
    def:pom-fibonacci-cube -/
theorem fibCubeAdj_of_ne_hamming_one {m : Nat} {x y : X m}
    (hne : x ≠ y) (hd : hammingDist x.1 y.1 = 1) : fibCubeAdj x y :=
  ⟨hne, hd⟩

/-- Paper wrapper: Fibonacci cube graph Γ_n has vertex set X_n with
    adjacency given by Hamming distance 1 among No11 words.
    def:pom-fibonacci-cube -/
theorem paper_pom_fibonacci_cube (m : Nat) :
    (∀ x : X m, ¬fibCubeAdj x x) ∧
    (∀ x y : X m, fibCubeAdj x y → fibCubeAdj y x) ∧
    (∀ x y : X m, fibCubeAdj x y → hammingDist x.1 y.1 = 1) := by
  exact ⟨fibCubeAdj_irrefl, fibCubeAdj_symm, fun _ _ h => h.2⟩

end Omega.Combinatorics.FibonacciCubeGraph
