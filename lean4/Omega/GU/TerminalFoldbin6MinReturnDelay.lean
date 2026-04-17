import Omega.Folding.BinFold

namespace Omega.GU

/-- One local step of the window-6 hypercube scan flips exactly one bit. -/
def terminalFoldbin6CubeStep (a b : Fin 64) : Prop :=
  hammingDist (intToWord 6 a.1) (intToWord 6 b.1) = 1

/-- Any finite one-step path in the window-6 hypercube has length at least the Hamming distance
between its endpoints. -/
theorem terminalFoldbin6_path_length_ge_endpoint_hamming :
    ∀ {start : Fin 64} {tail : List (Fin 64)},
      List.IsChain terminalFoldbin6CubeStep (start :: tail) →
        hammingDist (intToWord 6 start.1) (intToWord 6 (tail.getLastD start).1) ≤ tail.length
  | start, [], _ => by
      simp [hammingDist_self]
  | start, next :: tail, hChain => by
      rcases List.isChain_cons_cons.mp hChain with ⟨hStep, hTail⟩
      have hIH :
          hammingDist (intToWord 6 next.1) (intToWord 6 (tail.getLastD next).1) ≤ tail.length :=
        terminalFoldbin6_path_length_ge_endpoint_hamming hTail
      have hStepLe :
          hammingDist (intToWord 6 start.1) (intToWord 6 next.1) ≤ 1 := by
        simpa [terminalFoldbin6CubeStep] using le_of_eq hStep
      calc
        hammingDist (intToWord 6 start.1) (intToWord 6 ((next :: tail).getLastD start).1)
            = hammingDist (intToWord 6 start.1) (intToWord 6 (tail.getLastD next).1) := by
              rw [List.getLastD_cons]
        _ ≤ hammingDist (intToWord 6 start.1) (intToWord 6 next.1) +
              hammingDist (intToWord 6 next.1) (intToWord 6 (tail.getLastD next).1) :=
            hammingDist_triangle _ _ _
        _ ≤ 1 + tail.length := Nat.add_le_add hStepLe hIH
        _ = (next :: tail).length := by rw [Nat.add_comm]; simp

/-- If two distinct points of the same window-6 BinFold fiber occur as the endpoints of a path,
their endpoint Hamming distance is bounded below by the fiber minimum Hamming distance. -/
theorem terminalFoldbin6_endpoint_hamming_ge_fiber_min
    {start finish : Fin 64}
    (hReturn : cBinFold 6 start.1 = cBinFold 6 finish.1)
    (hDistinct : start ≠ finish) :
    cBinFiberMinHamming 6 (cBinFold 6 start.1) ≤
      hammingDist (intToWord 6 start.1) (intToWord 6 finish.1) := by
  let x := cBinFold 6 start.1
  let preimages := (Finset.range 64).filter (fun N => cBinFold 6 N = x)
  let pairs := preimages.product preimages |>.filter (fun (a, b) => a < b)
  have hstart : start.1 ∈ preimages := by
    simp [preimages, x, start.isLt]
  have hfinish : finish.1 ∈ preimages := by
    simp [preimages, x, finish.isLt, hReturn]
  have hvalne : start.1 ≠ finish.1 := by
    intro hEq
    exact hDistinct (Fin.ext hEq)
  rcases Nat.lt_or_gt_of_ne hvalne with hlt | hgt
  · have hpairs : pairs.Nonempty := by
      refine ⟨(start.1, finish.1), ?_⟩
      simp [pairs, hstart, hfinish, hlt]
    have hle :
        pairs.inf' hpairs (fun p => hammingDist (intToWord 6 p.1) (intToWord 6 p.2)) ≤
          hammingDist (intToWord 6 start.1) (intToWord 6 finish.1) :=
      Finset.inf'_le (s := pairs)
        (f := fun p => hammingDist (intToWord 6 p.1) (intToWord 6 p.2))
        (b := (start.1, finish.1)) (by simp [pairs, hstart, hfinish, hlt])
    unfold cBinFiberMinHamming
    dsimp [x, preimages, pairs]
    split_ifs with h
    · change pairs.inf' h (fun p => hammingDist (intToWord 6 p.1) (intToWord 6 p.2)) ≤
          hammingDist (intToWord 6 start.1) (intToWord 6 finish.1)
      simpa using hle
    · exact (h hpairs).elim
  · have hpairs : pairs.Nonempty := by
      refine ⟨(finish.1, start.1), ?_⟩
      simp [pairs, hstart, hfinish, hgt]
    have hle :
        pairs.inf' hpairs (fun p => hammingDist (intToWord 6 p.1) (intToWord 6 p.2)) ≤
          hammingDist (intToWord 6 finish.1) (intToWord 6 start.1) :=
      Finset.inf'_le (s := pairs)
        (f := fun p => hammingDist (intToWord 6 p.1) (intToWord 6 p.2))
        (b := (finish.1, start.1)) (by simp [pairs, hstart, hfinish, hgt])
    unfold cBinFiberMinHamming
    dsimp [x, preimages, pairs]
    split_ifs with h
    · change pairs.inf' h (fun p => hammingDist (intToWord 6 p.1) (intToWord 6 p.2)) ≤
          hammingDist (intToWord 6 start.1) (intToWord 6 finish.1)
      simpa [hammingDist_comm] using hle
    · exact (h hpairs).elim

/-- Paper-facing return-delay lower bound for repeated window-6 stable types along a local
one-bit scan path.
    cor:terminal-foldbin6-min-return-delay -/
theorem paper_terminal_foldbin6_min_return_delay
    {start : Fin 64} {tail : List (Fin 64)}
    (hChain : List.IsChain terminalFoldbin6CubeStep (start :: tail))
    (hReturn : cBinFold 6 start.1 = cBinFold 6 (tail.getLastD start).1)
    (hDistinct : start ≠ tail.getLastD start) :
    cBinFiberMinHamming 6 (cBinFold 6 start.1) ≤ tail.length := by
  exact
    le_trans
      (terminalFoldbin6_endpoint_hamming_ge_fiber_min hReturn hDistinct)
      (terminalFoldbin6_path_length_ge_endpoint_hamming hChain)

end Omega.GU
