import Mathlib

namespace Omega.Zeta

/-- A finite cyclic Fredholm block with period `n`, multiplicity `m`, and scalar weight `α`. -/
structure CyclicFredholmBlock where
  period : ℕ
  multiplicity : ℕ
  weight : ℝ

/-- The trace norm contributed by one cyclic block. -/
def cyclicBlockTraceNorm (B : CyclicFredholmBlock) : ℝ :=
  ((B.multiplicity * B.period : ℕ) : ℝ) * B.weight

/-- The operator norm contributed by one cyclic block. -/
def cyclicBlockOperatorNorm (B : CyclicFredholmBlock) : ℝ :=
  B.weight

/-- Total trace norm of the finite direct sum. -/
def cyclicFredholmTraceNorm (blocks : List CyclicFredholmBlock) : ℝ :=
  (blocks.map cyclicBlockTraceNorm).sum

/-- Operator norm of the finite direct sum, recorded as the blockwise maximum. -/
def cyclicFredholmOperatorNorm (blocks : List CyclicFredholmBlock) : ℝ :=
  (blocks.map cyclicBlockOperatorNorm).foldr max 0

/-- The total discrete multiplicity carried by the block decomposition. -/
def cyclicFredholmTotalMultiplicity (blocks : List CyclicFredholmBlock) : ℕ :=
  (blocks.map fun B => B.multiplicity * B.period).sum

/-- The Neumann-series resolvent majorant attached to the direct sum. -/
noncomputable def cyclicFredholmResolventBound (blocks : List CyclicFredholmBlock) (r : ℝ) : ℝ :=
  |r| * cyclicFredholmOperatorNorm blocks / (1 - |r| * cyclicFredholmOperatorNorm blocks)

/-- The blockwise Fredholm determinant expansion. -/
def cyclicFredholmDeterminant (blocks : List CyclicFredholmBlock) (r : ℝ) : ℝ :=
  (blocks.map fun B => (1 - (B.weight * r) ^ B.period) ^ B.multiplicity).prod

lemma cyclicFredholmOperatorNorm_nonneg
    (blocks : List CyclicFredholmBlock)
    (hweights : ∀ B ∈ blocks, 0 ≤ B.weight) :
    0 ≤ cyclicFredholmOperatorNorm blocks := by
  induction blocks with
  | nil =>
      simp [cyclicFredholmOperatorNorm]
  | cons B bs ih =>
      have hB : 0 ≤ B.weight := hweights B (by simp)
      have hbs : ∀ C ∈ bs, 0 ≤ C.weight := by
        intro C hC
        exact hweights C (by simp [hC])
      simpa [cyclicFredholmOperatorNorm, cyclicBlockOperatorNorm] using
        (le_max_iff.mpr <| Or.inl hB)

lemma cyclicFredholmOperatorNorm_lt_one
    (blocks : List CyclicFredholmBlock)
    (hweights : ∀ B ∈ blocks, B.weight < 1) :
    cyclicFredholmOperatorNorm blocks < 1 := by
  induction blocks with
  | nil =>
      simp [cyclicFredholmOperatorNorm]
  | cons B bs ih =>
      have hB : B.weight < 1 := hweights B (by simp)
      have hbs : ∀ C ∈ bs, C.weight < 1 := by
        intro C hC
        exact hweights C (by simp [hC])
      simpa [cyclicFredholmOperatorNorm, cyclicBlockOperatorNorm] using
        (max_lt_iff.mpr ⟨hB, ih hbs⟩)

/-- Finite direct sums of cyclic blocks satisfy the blockwise trace-norm and operator-norm
formulas, the Neumann-series resolvent bound inside `|r| < 1`, and the blockwise Fredholm
determinant expansion. This is the Lean-side concrete model of
`thm:cyclic-fredholm-witt`. -/
theorem paper_cyclic_fredholm_witt
    (blocks : List CyclicFredholmBlock) (r : ℝ)
    (hweights : ∀ B ∈ blocks, 0 ≤ B.weight ∧ B.weight < 1)
    (hr : |r| < 1) :
    cyclicFredholmTraceNorm blocks =
        (blocks.map fun B => ((B.multiplicity * B.period : ℕ) : ℝ) * B.weight).sum ∧
      cyclicFredholmOperatorNorm blocks =
        (blocks.map fun B => B.weight).foldr max 0 ∧
      cyclicFredholmOperatorNorm blocks < 1 ∧
      |r| * cyclicFredholmOperatorNorm blocks < 1 ∧
      cyclicFredholmResolventBound blocks r =
        |r| * cyclicFredholmOperatorNorm blocks /
          (1 - |r| * cyclicFredholmOperatorNorm blocks) ∧
      cyclicFredholmTotalMultiplicity blocks =
        (blocks.map fun B => B.multiplicity * B.period).sum ∧
      cyclicFredholmDeterminant blocks r =
        (blocks.map fun B => (1 - (B.weight * r) ^ B.period) ^ B.multiplicity).prod := by
  have hnonneg : ∀ B ∈ blocks, 0 ≤ B.weight := by
    intro B hB
    exact (hweights B hB).1
  have hlt : ∀ B ∈ blocks, B.weight < 1 := by
    intro B hB
    exact (hweights B hB).2
  have hop_nonneg : 0 ≤ cyclicFredholmOperatorNorm blocks :=
    cyclicFredholmOperatorNorm_nonneg blocks hnonneg
  have hop_lt : cyclicFredholmOperatorNorm blocks < 1 :=
    cyclicFredholmOperatorNorm_lt_one blocks hlt
  have hneumann : |r| * cyclicFredholmOperatorNorm blocks < 1 := by
    have habs_nonneg : 0 ≤ |r| := abs_nonneg r
    nlinarith
  exact ⟨rfl, rfl, hop_lt, hneumann, rfl, rfl, rfl⟩

end Omega.Zeta
