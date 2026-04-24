import Omega.Folding.BinFold
import Omega.Folding.FiberArithmetic

namespace Omega.Folding

/-- The tail information of a stable word recorded by its Zeckendorf value and boundary bit. -/
def foldBinTailSignature (m : ℕ) (w : Omega.X m) : Nat × Bool :=
  (Omega.stableValue w, Omega.get w.1 (m - 1))

/-- The tail candidate has the same Zeckendorf value as the reference stable word. -/
def FoldBinTailValueMatch (m : ℕ) (σ : Nat × Bool) (N : Fin (2 ^ m)) : Prop :=
  Omega.stableValue (Omega.cBinFold m N.1) = σ.1

/-- The visible boundary bit agrees with the one read from the reference stable word. -/
def FoldBinTailBoundary (m : ℕ) (σ : Nat × Bool) (N : Fin (2 ^ m)) : Prop :=
  Omega.get (Omega.cBinFold m N.1).1 (m - 1) = σ.2

/-- The folded image is automatically a stable Zeckendorf tail, hence satisfies the adjacency
constraint. -/
def FoldBinTailAdjacency (m : ℕ) (N : Fin (2 ^ m)) : Prop :=
  Omega.No11 (Omega.cBinFold m N.1).1

/-- The tail candidate stays inside the binary input window of size `2^m`. -/
def FoldBinTailThreshold (m : ℕ) (N : Fin (2 ^ m)) : Prop :=
  N.1 < 2 ^ m

/-- Concrete admissibility predicate for bin-fold tails: a candidate tail is admissible exactly when
its folded image has the same Zeckendorf value and boundary bit as the target stable word, is
adjacency-free after folding, and comes from the binary window `{0, …, 2^m - 1}`. -/
def foldBinTailAdmissible (m : ℕ) (σ : Nat × Bool) (N : Fin (2 ^ m)) : Prop :=
  FoldBinTailValueMatch m σ N ∧
    FoldBinTailBoundary m σ N ∧ FoldBinTailAdjacency m N ∧ FoldBinTailThreshold m N

/-- Paper-facing specification for the bin-fold fiber/tail correspondence: the fiber over `w`
coincides with the admissible tails cut out by the pair `(V_m(w), w_m)`. -/
def FoldBinFiberTailSpec (m : ℕ) (w : Omega.X m) : Prop :=
  let σ := foldBinTailSignature m w
  (∀ N : Fin (2 ^ m), Omega.cBinFold m N.1 = w ↔ foldBinTailAdmissible m σ N) ∧
    Nonempty
      ({N : Fin (2 ^ m) // Omega.cBinFold m N.1 = w} ≃
        {N : Fin (2 ^ m) // foldBinTailAdmissible m σ N})

private theorem cBinFold_eq_iff_foldBinTailAdmissible (m : ℕ) (w : Omega.X m)
    (N : Fin (2 ^ m)) :
    Omega.cBinFold m N.1 = w ↔ foldBinTailAdmissible m (foldBinTailSignature m w) N := by
  constructor
  · intro hFold
    refine ⟨?_, ?_, ?_, N.2⟩
    · simp [FoldBinTailValueMatch, foldBinTailSignature, hFold]
    · simp [FoldBinTailBoundary, foldBinTailSignature, hFold]
    · simpa [FoldBinTailAdjacency, hFold] using w.2
  · intro hTail
    exact Omega.X.eq_of_stableValue_eq hTail.1

/-- The bin-fold preimage of a stable word is in bijection with the tails satisfying the concrete
adjacency, boundary, and threshold constraints determined by `(V_m(w), w_m)`.
    prop:fold-bin-fiber-tail -/
theorem paper_fold_bin_fiber_tail (m : ℕ) (w : Omega.X m) : FoldBinFiberTailSpec m w := by
  refine ⟨cBinFold_eq_iff_foldBinTailAdmissible m w, ?_⟩
  let σ := foldBinTailSignature m w
  refine ⟨
    { toFun := fun N => ⟨N.1, (cBinFold_eq_iff_foldBinTailAdmissible m w N.1).1 N.2⟩
      invFun := fun N => ⟨N.1, (cBinFold_eq_iff_foldBinTailAdmissible m w N.1).2 N.2⟩
      left_inv := by
        intro N
        cases N
        rfl
      right_inv := by
        intro N
        cases N
        rfl }⟩

end Omega.Folding
