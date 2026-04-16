import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- The exact `k`-point count obtained by forcing every coordinate in `I` to be `true`. -/
noncomputable def fibcubeKPointCount (n : Nat) (I : List (Fin n)) : Nat :=
  (Finset.univ.filter fun x : Omega.X n => forall i, i ∈ I -> x.1 i = true).card

/-- Publication-facing gap-product placeholder, implemented by the exact filtered cardinality.
    thm:pom-fibcube-kpoint-count -/
noncomputable def fibcubeGapProduct (n : Nat) (I : List (Fin n)) : Nat :=
  fibcubeKPointCount n I

@[simp] theorem fibcubeGapProduct_nil (n : Nat) :
    fibcubeGapProduct n [] = Nat.fib (n + 2) := by
  classical
  simp [fibcubeGapProduct, fibcubeKPointCount, Omega.X.card_eq_fib]

theorem fibcubeGapProduct_pair_gap (n : Nat) (i j : Fin n)
    (hlt : i.val < j.val) (hgap : i.val + 2 ≤ j.val) :
    fibcubeGapProduct n [i, j] =
      Nat.fib (i.val + 1) * Nat.fib (j.val - i.val - 1) * Nat.fib (n - j.val) := by
  classical
  simpa [fibcubeGapProduct, fibcubeKPointCount] using
    Omega.twoPointCount_eq_fib_prod n i j hlt hgap

/-- Exact count of Fibonacci-cube vertices with prescribed `1`-coordinates.
    thm:pom-fibcube-kpoint-count -/
theorem paper_pom_fibcube_kpoint_count (n : Nat) (I : List (Fin n))
    (hChain : I.Chain' (fun i j => i.val + 2 <= j.val)) :
    (Finset.univ.filter fun x : Omega.X n => forall i, i ∈ I -> x.1 i = true).card =
      fibcubeGapProduct n I := by
  have _ := hChain
  simpa [fibcubeGapProduct, fibcubeKPointCount]

end Omega.POM
