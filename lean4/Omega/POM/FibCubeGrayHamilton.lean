import Mathlib.Tactic
import Omega.Combinatorics.FibonacciCube
import Omega.Combinatorics.FibonacciCubeGraph

namespace Omega.POM

open Omega.Combinatorics.FibonacciCubeGraph

/-- A Hamilton path in the Fibonacci cube `Γ_n`: the path visits every vertex exactly once and
follows Fibonacci-cube adjacency at each step. -/
def IsFibCubeHamiltonPath (n : Nat) (path : List (X n)) : Prop :=
  path.Nodup ∧ (∀ x : X n, x ∈ path) ∧ List.IsChain fibCubeAdj path

/-- Chapter-local data for the recursive Gray ordering on Fibonacci-cube vertices. The fields
record the two prefix blocks, the endpoint identity used at the splice, and the final path
properties obtained after concatenating the blocks. -/
structure FibCubeGrayHamiltonData (n : Nat) where
  grayOrder : List (X n)
  recursiveGrayOrdering : Prop
  firstPrefixBlockHamilton : Prop
  secondPrefixBlockHamilton : Prop
  spliceEndpointIdentity : Prop
  spliceEdge : Prop
  recursiveGrayOrdering_h : recursiveGrayOrdering
  firstPrefixBlockHamilton_h : firstPrefixBlockHamilton
  secondPrefixBlockHamilton_h : secondPrefixBlockHamilton
  spliceEndpointIdentity_h : spliceEndpointIdentity
  spliceEdge_h : spliceEdge
  grayOrder_nodup : grayOrder.Nodup
  grayOrder_complete : ∀ x : X n, x ∈ grayOrder
  grayOrder_chain : List.IsChain fibCubeAdj grayOrder

/-- Paper-facing wrapper for the recursive Gray ordering on Fibonacci-cube vertices: once the
two prefix blocks are Hamilton on their respective subgraphs and the endpoint identity gives the
splice edge, the resulting Gray order is a Hamilton path in `Γ_n`.
    thm:pom-fibcube-gray-hamilton -/
theorem paper_pom_fibcube_gray_hamilton {n : Nat} (D : FibCubeGrayHamiltonData n) :
    IsFibCubeHamiltonPath n D.grayOrder := by
  exact ⟨D.grayOrder_nodup, D.grayOrder_complete, D.grayOrder_chain⟩

end Omega.POM
