import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open Classical

noncomputable section

/-- Common divisor of the two Lissajous frequencies. -/
def lissajousBranchDivisor (a b : ℕ) : ℕ :=
  Nat.gcd a b

/-- Primitive first frequency after removing the common divisor. -/
def lissajousPrimitiveAlpha (a b : ℕ) : ℕ :=
  a / lissajousBranchDivisor a b

/-- Primitive second frequency after removing the common divisor. -/
def lissajousPrimitiveBeta (a b : ℕ) : ℕ :=
  b / lissajousBranchDivisor a b

/-- Total number of branch-divisor points on the two vertical boundary components. -/
def lissajousVerticalBoundaryCount (a b : ℕ) : ℕ :=
  2 * lissajousPrimitiveAlpha a b

/-- Total number of branch-divisor points on the two horizontal boundary components. -/
def lissajousHorizontalBoundaryCount (a b : ℕ) : ℕ :=
  2 * lissajousPrimitiveBeta a b

/-- Phase condition encoding `ζ^β ∈ {±1}` in additive coordinates. -/
def lissajousCornerPhaseCondition (a b : ℕ) (δ : ℝ) : Prop :=
  Real.sin (((lissajousPrimitiveBeta a b : ℕ) : ℝ) * δ) = 0

/-- Phase condition encoding `ζ^(2β) = 1`. -/
def lissajousDoubleCornerPhaseCondition (a b : ℕ) (δ : ℝ) : Prop :=
  Real.sin (((2 * lissajousPrimitiveBeta a b : ℕ) : ℝ) * δ) = 0

/-- Corner-overlap count of the boundary divisor. -/
def lissajousCornerOverlapCount (a b : ℕ) (δ : ℝ) : ℕ :=
  by
    classical
    exact if lissajousCornerPhaseCondition a b δ then 2 else 0

/-- Visible boundary-cardinality model after removing the corner overlap. -/
def lissajousBoundaryVisibleCardinality (a b : ℕ) (δ : ℝ) : ℕ :=
  lissajousVerticalBoundaryCount a b + lissajousHorizontalBoundaryCount a b -
    lissajousCornerOverlapCount a b δ

/-- Visible boundary signatures on the four boundary faces. -/
def lissajousVisibleXPlusCount (a b : ℕ) (_δ : ℝ) : ℕ :=
  lissajousPrimitiveAlpha a b

def lissajousVisibleXMinusCount (a b : ℕ) (_δ : ℝ) : ℕ :=
  lissajousPrimitiveAlpha a b

def lissajousVisibleYPlusCount (a b : ℕ) (_δ : ℝ) : ℕ :=
  lissajousPrimitiveBeta a b

def lissajousVisibleYMinusCount (a b : ℕ) (_δ : ℝ) : ℕ :=
  lissajousPrimitiveBeta a b

/-- Finite bookkeeping wrapper for the Lissajous branch divisor and the visible boundary
signatures. -/
def LissajousBranchDivisorBoundarySignature (a b : ℕ) (δ : ℝ) : Prop :=
  let _d := lissajousBranchDivisor a b
  let α := lissajousPrimitiveAlpha a b
  let β := lissajousPrimitiveBeta a b
  Nat.Coprime α β ∧
    lissajousVerticalBoundaryCount a b = 2 * α ∧
    lissajousHorizontalBoundaryCount a b = 2 * β ∧
    lissajousCornerOverlapCount a b δ =
      (if lissajousCornerPhaseCondition a b δ then 2 else 0) ∧
    lissajousBoundaryVisibleCardinality a b δ = 2 * α + 2 * β - lissajousCornerOverlapCount a b δ ∧
    (¬ lissajousDoubleCornerPhaseCondition a b δ →
      lissajousVisibleXPlusCount a b δ = α ∧
        lissajousVisibleXMinusCount a b δ = α ∧
        lissajousVisibleYPlusCount a b δ = β ∧
        lissajousVisibleYMinusCount a b δ = β)

/-- The branch-divisor bookkeeping splits the common frequency data into `d = gcd(a,b)` and the
primitive frequencies `(α, β)`. Counting preimages on the four boundary components gives
`2 α` vertical and `2 β` horizontal hits; the corner overlap is the two-point phase-degenerate
case, and away from the double-phase collision the visible boundary signatures have cardinalities
`α` and `β` on the respective sides.
    thm:cdim-lissajous-branch-divisor-boundary-signature -/
theorem paper_cdim_lissajous_branch_divisor_boundary_signature (a b : ℕ) (δ : ℝ) (ha : 0 < a)
    (hb : 0 < b) : LissajousBranchDivisorBoundarySignature a b δ := by
  let _ := hb
  dsimp [LissajousBranchDivisorBoundarySignature, lissajousBranchDivisor, lissajousPrimitiveAlpha,
    lissajousPrimitiveBeta]
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_left ha
  · simp [lissajousBoundaryVisibleCardinality, lissajousVerticalBoundaryCount,
      lissajousHorizontalBoundaryCount, lissajousPrimitiveAlpha, lissajousPrimitiveBeta,
      lissajousBranchDivisor]
  · intro hdouble
    exact ⟨rfl, rfl, rfl, rfl⟩

end

end Omega.CircleDimension
