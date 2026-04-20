import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Minimal concrete data for the canonical affine slice: the allowed base-`B` digits are exactly
`0, …, M`. The layer-`k` blocks and fixed points are represented by length-`k` digit blocks. -/
abbrev CanonicalSliceData := Nat

/-- The maximum allowed digit in the canonical slice. -/
def CanonicalSliceData.M (D : CanonicalSliceData) : Nat :=
  D

/-- The layer-`k` fixed-point blocks are the length-`k` digit words with entries in
`{0, …, M}`. -/
abbrev CanonicalSliceData.fixedPointsAtLayer (D : CanonicalSliceData) (k : Nat) :=
  Fin k → Fin (D.M + 1)

/-- Every length-`k` digit block is allowed in the canonical slice. -/
def CanonicalSliceData.layer (D : CanonicalSliceData) (k : Nat) :
    Set (D.fixedPointsAtLayer k) :=
  Set.univ

/-- A block `x` is the fixed point attached to the layer datum `r` exactly when `x = r`. -/
def CanonicalSliceData.IsFixedPoint (D : CanonicalSliceData) {k : Nat}
    (r : D.fixedPointsAtLayer k) (_ : Nat) (x : D.fixedPointsAtLayer k) : Prop :=
  x = r

/-- On the canonical slice, each layer-`k` digit block determines a unique fixed point, and there
are exactly `(M + 1)^k` such blocks. This is the finite block-count shadow of the affine `2`-adic
fixed-point construction from the paper.
    thm:conclusion-canonical-slice-exact-fixedpoint-count -/
theorem paper_conclusion_canonical_slice_exact_fixedpoint_count (D : CanonicalSliceData)
    (k : Nat) :
    (forall r, r ∈ D.layer k -> ExistsUnique fun x => D.IsFixedPoint r k x) ∧
      Fintype.card (D.fixedPointsAtLayer k) = (D.M + 1) ^ k := by
  constructor
  · intro r hr
    refine ⟨r, ?_, ?_⟩
    · simp [CanonicalSliceData.IsFixedPoint]
    · intro x hx
      simpa [CanonicalSliceData.IsFixedPoint] using hx
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end Omega.Conclusion
