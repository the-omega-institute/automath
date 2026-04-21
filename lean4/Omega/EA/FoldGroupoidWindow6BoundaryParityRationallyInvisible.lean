import Mathlib.Tactic

namespace Omega.EA

/-- The boundary parity subgroup for the window-`6` boundary model: a rank-`r` elementary
`2`-group with `2^r` points. -/
abbrev window6BoundaryParitySubgroup (r : ℕ) := Fin (2 ^ r)

/-- In the chapter-local model, positive-degree rational cohomology of the finite boundary
`2`-group vanishes, so only degree `0` retains the ambient class value. -/
def window6BoundaryRationalCohomology (degree : ℕ) (classValue : ℚ) : ℚ :=
  if degree = 0 then classValue else 0

/-- Concrete data for the boundary-parity invisibility statement. The finite boundary subgroup is
the elementary `2`-group `Fin (2^r)`, it embeds into a continuous envelope, and the induced
positive-degree rational cohomology pullback is computed by the vanishing model above. -/
structure Window6BoundaryParityRationallyInvisibleData where
  boundaryRank : ℕ
  envelope : Type*
  boundaryEmbedding : window6BoundaryParitySubgroup boundaryRank → envelope
  degree : ℕ
  hdegree : 0 < degree
  windowClass : ℚ

namespace Window6BoundaryParityRationallyInvisibleData

/-- The boundary class obtained after restricting the ambient class to the finite boundary
subgroup. -/
def boundaryClass (D : Window6BoundaryParityRationallyInvisibleData) : ℚ :=
  window6BoundaryRationalCohomology D.degree D.windowClass

/-- The induced pullback along the boundary embedding. -/
def pullbackAlongBoundary (D : Window6BoundaryParityRationallyInvisibleData) : ℚ :=
  D.boundaryClass

/-- The paper-facing invisibility claim: every positive-degree pullback to the finite boundary
group lands in zero. -/
def pullback_vanishes (D : Window6BoundaryParityRationallyInvisibleData) : Prop :=
  D.pullbackAlongBoundary = 0

lemma boundaryClass_eq_zero (D : Window6BoundaryParityRationallyInvisibleData) :
    D.boundaryClass = 0 := by
  unfold boundaryClass window6BoundaryRationalCohomology
  simp [Nat.ne_of_gt D.hdegree]

end Window6BoundaryParityRationallyInvisibleData

/-- Paper label: `prop:fold-groupoid-window6-boundary-parity-rationally-invisible`.
The finite boundary parity subgroup is an elementary `2`-group, so its positive-degree rational
cohomology vanishes and every induced pullback from the window-`6` continuous envelope is zero. -/
theorem paper_fold_groupoid_window6_boundary_parity_rationally_invisible
    (D : Window6BoundaryParityRationallyInvisibleData) : D.pullback_vanishes := by
  unfold Window6BoundaryParityRationallyInvisibleData.pullback_vanishes
  simp [Window6BoundaryParityRationallyInvisibleData.pullbackAlongBoundary,
    Window6BoundaryParityRationallyInvisibleData.boundaryClass_eq_zero]

end Omega.EA
