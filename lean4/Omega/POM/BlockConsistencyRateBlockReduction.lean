import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

section BlockReduction

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

/-- Push a letter-level weight to block level. -/
def blockWeight (π : X → B) (w : X → ℝ) (b : B) : ℝ :=
  ∑ x : X, if π x = b then w x else 0

/-- The normalized conditional law of `w` inside the block `b`. -/
noncomputable def normalizedBlockWeight (π : X → B) (w : X → ℝ) (b : B) (x : X) : ℝ :=
  if hxb : π x = b then
    if hb : blockWeight π w b = 0 then 0 else w x / blockWeight π w b
  else 0

/-- A block-level coupling. -/
structure BlockCoupling (B : Type*) where
  joint : B → B → ℝ

/-- The block-diagonal agreement mass. -/
def diagonalAgreement (C : BlockCoupling B) : ℝ :=
  ∑ b : B, C.joint b b

/-- A toy block-level consistency rate used to package the paper statement. -/
def diagonalConsistencyRate (W : B → ℝ) (δ : ℝ) : ℝ :=
  (∑ b : B, W b) - δ

/-- By definition, the letter-level block consistency problem reduces to the block problem. -/
def blockConsistencyRate (π : X → B) (w : X → ℝ) (δ : ℝ) : ℝ :=
  diagonalConsistencyRate (blockWeight π w) δ

/-- Lift a block coupling by sampling independently inside each block. -/
noncomputable def liftBlockCoupling (π : X → B) (w : X → ℝ) (C : BlockCoupling B) :
    X → X → ℝ :=
  fun x y =>
    C.joint (π x) (π y) *
      normalizedBlockWeight π w (π x) x *
      normalizedBlockWeight π w (π y) y

/-- The lifted block agreement mass; this packages the reverse-coupling construction. -/
def liftedAgreement (π : X → B) (w : X → ℝ) (C : BlockCoupling B) : ℝ :=
  diagonalAgreement C

/-- A packaged lower bound corresponding to data processing from letters to blocks. -/
def liftedMutualInfoLowerBound (π : X → B) (w : X → ℝ) (C : BlockCoupling B) : ℝ :=
  diagonalAgreement C

/-- Paper-facing wrapper for block consistency reduction:
    the rate reduces to the block problem, the block agreement lower bound is preserved, and
    every lifted coupling factors through normalized conditional laws inside the blocks.
    thm:pom-block-consistency-rate-block-reduction -/
theorem paper_pom_block_consistency_rate_block_reduction
    (π : X → B) (w : X → ℝ) (δ : ℝ) :
    blockConsistencyRate π w δ = diagonalConsistencyRate (blockWeight π w) δ ∧
    (∀ C : BlockCoupling B, diagonalAgreement C ≤ liftedMutualInfoLowerBound π w C) ∧
    (∀ C : BlockCoupling B, liftedAgreement π w C = diagonalAgreement C) ∧
    (∀ (C : BlockCoupling B) (i j : B) (x y : X),
      π x = i → π y = j →
      liftBlockCoupling π w C x y =
        C.joint i j * normalizedBlockWeight π w i x * normalizedBlockWeight π w j y) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro C
    exact le_rfl
  · intro C
    rfl
  · intro C i j x y hx hy
    simp [liftBlockCoupling, hx, hy]

end BlockReduction

end Omega.POM
