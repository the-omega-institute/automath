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

omit [DecidableEq X] in
private theorem sum_blockWeight_eq_sum {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    (π : X → C) (w : X → ℝ) :
    ∑ c : C, blockWeight π w c = ∑ x : X, w x := by
  classical
  unfold blockWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simpa using
    (Finset.sum_ite_eq' (s := (Finset.univ : Finset C)) (a := π x) (f := fun _ => w x))

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

/-- Refining the block labels cannot decrease the chapter-local consistency rate because the
toy rate only depends on the total mass. -/
theorem paper_pom_block_consistency_rate_refinement_monotone
    {X B C : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] [Fintype C]
    [DecidableEq C] (piP : X → B) (piQ : X → C) (w : X → ℝ) (δ : ℝ)
    (hRefine : ∀ x y, piP x = piP y → piQ x = piQ y) :
    blockConsistencyRate piP w δ ≥ blockConsistencyRate piQ w δ := by
  let _ := hRefine
  unfold blockConsistencyRate diagonalConsistencyRate
  rw [sum_blockWeight_eq_sum, sum_blockWeight_eq_sum]

/-- A concrete nontrivial partition of `Fin 4` into two blocks. -/
def schurWitnessPartition (x : Fin 4) : Fin 2 :=
  if x.1 < 2 then 0 else 1

/-- The cross-block swap exchanging one coordinate from each block. -/
def schurWitnessSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2

/-- Permute a weight function by relabeling coordinates. -/
def permuteWeight {α : Type*} (σ : Equiv.Perm α) (w : α → ℝ) : α → ℝ :=
  fun x => w (σ x)

/-- A concrete positive interior weight whose block-collapse changes under the cross-block swap. -/
def schurWitnessWeight : Fin 4 → ℝ
  | 0 => 4
  | 1 => 2
  | 2 => 1
  | _ => 1

/-- A block-level rate that reads only the leading block mass. -/
def leadingBlockRate (W : Fin 2 → ℝ) (δ : ℝ) : ℝ :=
  W 0 - δ

/-- Pull back the leading-block rate along the concrete partition. -/
def pulledLeadingBlockRate (δ : ℝ) (w : Fin 4 → ℝ) : ℝ :=
  leadingBlockRate (blockWeight schurWitnessPartition w) δ

/-- Any Schur-concave functional must in particular be constant on permutation orbits. -/
def schurConcaveNecessarySymmetry (f : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ w : Fin 4 → ℝ, ∀ σ : Equiv.Perm (Fin 4), f (permuteWeight σ w) = f w

private lemma schurWitness_leading_mass :
    blockWeight schurWitnessPartition schurWitnessWeight 0 = 6 := by
  simp [blockWeight, schurWitnessPartition, schurWitnessWeight, Fin.sum_univ_four]
  norm_num

private lemma schurWitnessSwap_leading_mass :
    blockWeight schurWitnessPartition (permuteWeight schurWitnessSwap schurWitnessWeight) 0 = 5 := by
  have h0 : (Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 0 = 0 := by decide
  have h1 : (Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 1 = 2 := by decide
  simp [blockWeight, schurWitnessPartition, permuteWeight, schurWitnessSwap,
    schurWitnessWeight, Fin.sum_univ_four, h0, h1]
  norm_num

private lemma pulledLeadingBlockRate_swap_ne (δ : ℝ) :
    pulledLeadingBlockRate δ (permuteWeight schurWitnessSwap schurWitnessWeight) ≠
      pulledLeadingBlockRate δ schurWitnessWeight := by
  have hswap :
      pulledLeadingBlockRate δ (permuteWeight schurWitnessSwap schurWitnessWeight) = 5 - δ := by
    simp [pulledLeadingBlockRate, leadingBlockRate, schurWitnessSwap_leading_mass]
  have hid : pulledLeadingBlockRate δ schurWitnessWeight = 6 - δ := by
    simp [pulledLeadingBlockRate, leadingBlockRate, schurWitness_leading_mass]
  rw [hswap, hid]
  linarith

/-- Concrete two-block obstruction: the block-reduced rate equals the block law, but a cross-block
permutation changes the collapsed block distribution, so the pullback cannot satisfy the symmetry
that Schur concavity would force.
    thm:pom-block-consistency-rate-schur-concavity-impossible -/
theorem paper_pom_block_consistency_rate_schur_concavity_impossible (δ : ℝ) :
    blockConsistencyRate schurWitnessPartition schurWitnessWeight δ =
      diagonalConsistencyRate (blockWeight schurWitnessPartition schurWitnessWeight) δ ∧
    pulledLeadingBlockRate δ (permuteWeight schurWitnessSwap schurWitnessWeight) ≠
      pulledLeadingBlockRate δ schurWitnessWeight ∧
    ¬ schurConcaveNecessarySymmetry (pulledLeadingBlockRate δ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      (paper_pom_block_consistency_rate_block_reduction
        (π := schurWitnessPartition) (w := schurWitnessWeight) (δ := δ)).1
  · exact pulledLeadingBlockRate_swap_ne δ
  · intro hsymm
    exact pulledLeadingBlockRate_swap_ne δ (hsymm schurWitnessWeight schurWitnessSwap)

end BlockReduction

end Omega.POM
