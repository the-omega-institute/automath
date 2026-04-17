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

/-- A scan path has no dwell when every adjacent BinFold label changes. -/
def terminalFoldbin6NoDwell : List (Fin 64) → Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => cBinFold 6 a.1 ≠ cBinFold 6 b.1 ∧ terminalFoldbin6NoDwell (b :: tail)

private lemma binFiber6_minHamming_values (x : X 6) :
    cBinFiberMinHamming 6 x = 2 ∨ cBinFiberMinHamming 6 x = 3 ∨ cBinFiberMinHamming 6 x = 5 := by
  let s2 : Finset (X 6) := (@Finset.univ (X 6) (fintypeX 6)).filter
    (fun y => cBinFiberMinHamming 6 y = 2)
  let s3 : Finset (X 6) := (@Finset.univ (X 6) (fintypeX 6)).filter
    (fun y => cBinFiberMinHamming 6 y = 3)
  let s5 : Finset (X 6) := (@Finset.univ (X 6) (fintypeX 6)).filter
    (fun y => cBinFiberMinHamming 6 y = 5)
  have hs23 : Disjoint s2 s3 := by
    rw [Finset.disjoint_left]
    intro y hy2 hy3
    simp only [s2, s3, Finset.mem_filter, Finset.mem_univ, true_and] at hy2 hy3
    omega
  have hs25 : Disjoint s2 s5 := by
    rw [Finset.disjoint_left]
    intro y hy2 hy5
    simp only [s2, s5, Finset.mem_filter, Finset.mem_univ, true_and] at hy2 hy5
    omega
  have hs35 : Disjoint s3 s5 := by
    rw [Finset.disjoint_left]
    intro y hy3 hy5
    simp only [s3, s5, Finset.mem_filter, Finset.mem_univ, true_and] at hy3 hy5
    omega
  have hs235 : Disjoint (s2 ∪ s3) s5 := by
    rw [Finset.disjoint_left]
    intro y hy23 hy5
    rcases Finset.mem_union.mp hy23 with hy2 | hy3
    · exact (Finset.disjoint_left.mp hs25 hy2) hy5
    · exact (Finset.disjoint_left.mp hs35 hy3) hy5
  have hs2 : s2.card = 13 := by
    change cBinFiberMinHammingHist 6 2 = 13
    exact binFiber6_minHamming_hist_2
  have hs3 : s3.card = 6 := by
    change cBinFiberMinHammingHist 6 3 = 6
    exact binFiber6_minHamming_hist_3
  have hs5 : s5.card = 2 := by
    change cBinFiberMinHammingHist 6 5 = 2
    exact binFiber6_minHamming_hist_5
  have hcard :
      ((s2 ∪ s3) ∪ s5).card = Fintype.card (X 6) := by
    calc
      ((s2 ∪ s3) ∪ s5).card = (s2 ∪ s3).card + s5.card := Finset.card_union_of_disjoint hs235
      _ = s2.card + s3.card + s5.card := by rw [Finset.card_union_of_disjoint hs23]
      _ = 13 + 6 + 2 := by rw [hs2, hs3, hs5]
      _ = Fintype.card (X 6) := by
        rw [X.card_eq_fib]
        native_decide
  have hsubset : ((s2 ∪ s3) ∪ s5) ⊆ (Finset.univ : Finset (X 6)) := by
    intro y hy
    simp
  have hunion : ((s2 ∪ s3) ∪ s5) = (Finset.univ : Finset (X 6)) := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [Finset.card_univ, ← hcard]
  have hx : x ∈ ((s2 ∪ s3) ∪ s5) := by
    rw [hunion]
    simp
  rcases Finset.mem_union.mp hx with hx23 | hx5
  · rcases Finset.mem_union.mp hx23 with hx2 | hx3
    · exact Or.inl ((Finset.mem_filter.mp hx2).2)
    · exact Or.inr <| Or.inl ((Finset.mem_filter.mp hx3).2)
  · exact Or.inr <| Or.inr ((Finset.mem_filter.mp hx5).2)

private lemma terminalFoldbin6_step_changes_label {a b : Fin 64}
    (hStep : terminalFoldbin6CubeStep a b) :
    cBinFold 6 a.1 ≠ cBinFold 6 b.1 := by
  intro hSame
  have hne : a ≠ b := by
    intro hab
    have : hammingDist (intToWord 6 a.1) (intToWord 6 b.1) = 0 := by
      subst hab
      simp [hammingDist_self]
    rw [hStep] at this
    omega
  have hminle := terminalFoldbin6_endpoint_hamming_ge_fiber_min hSame hne
  have hvals := binFiber6_minHamming_values (cBinFold 6 a.1)
  have hge2 : 2 ≤ cBinFiberMinHamming 6 (cBinFold 6 a.1) := by
    rcases hvals with h2 | h3 | h5 <;> omega
  have : 2 ≤ 1 := by
    rw [hStep] at hminle
    exact le_trans hge2 hminle
  omega

/-- Any one-step window-6 scan path changes BinFold label at every adjacent step.
    cor:terminal-foldbin6-no-dwell -/
theorem paper_terminal_foldbin6_no_dwell {start : Fin 64} {tail : List (Fin 64)}
    (hChain : List.IsChain terminalFoldbin6CubeStep (start :: tail)) :
    terminalFoldbin6NoDwell (start :: tail) := by
  induction tail generalizing start with
  | nil =>
      simp [terminalFoldbin6NoDwell]
  | cons next tail ih =>
      rcases List.isChain_cons_cons.mp hChain with ⟨hStep, hTail⟩
      exact ⟨terminalFoldbin6_step_changes_label hStep, ih hTail⟩

end Omega.GU
