import Mathlib.Tactic

namespace Omega.POM

/-- A pure tensor in `q` factors is represented by its coordinates. -/
abbrev PureTensor (q : ℕ) (α : Type*) := Fin q → α

/-- The permutation action on pure tensors:
`(π(σ)v)_i = v_{σ⁻¹(i)}`. -/
def permutePureTensor {q : ℕ} {α : Type*} (σ : Equiv.Perm (Fin q))
    (v : PureTensor q α) : PureTensor q α :=
  v ∘ σ.symm

/-- Tensorizing an endomorphism means applying it to each tensor factor. -/
def tensorizedTransition {q : ℕ} {α : Type*} (T : α → α)
    (v : PureTensor q α) : PureTensor q α :=
  fun i => T (v i)

/-- The two transition branches indexed by `b ∈ {0,1}`. -/
def tensorTransitionFamily {q : ℕ} {α : Type*} (T₀ T₁ : α → α) :
    Bool → PureTensor q α → PureTensor q α
  | false => tensorizedTransition T₀
  | true => tensorizedTransition T₁

/-- A weighted pure tensor. This models one summand of the collision kernel. -/
abbrev WeightedPureTensor (q : ℕ) (α : Type*) := ℚ × PureTensor q α

/-- The branchwise tensor collision kernel `A_q^{ten} = G₀ ⊗ T₀^{⊗ q} + G₁ ⊗ T₁^{⊗ q}` recorded
as its two weighted summands. -/
def summedTensorCollisionKernel {q : ℕ} {α : Type*} (G₀ G₁ : ℚ) (T₀ T₁ : α → α)
    (v : PureTensor q α) : Bool → WeightedPureTensor q α
  | false => (G₀, tensorizedTransition T₀ v)
  | true => (G₁, tensorizedTransition T₁ v)

/-- Permuting only the tensor factor of a weighted pure tensor. -/
def permuteWeightedPureTensor {q : ℕ} {α : Type*} (σ : Equiv.Perm (Fin q))
    (w : WeightedPureTensor q α) : WeightedPureTensor q α :=
  (w.1, permutePureTensor σ w.2)

/-- Apply the permutation action branchwise to the summed tensor collision kernel. -/
def permuteSummedTensorCollisionKernel {q : ℕ} {α : Type*} (σ : Equiv.Perm (Fin q))
    (K : Bool → WeightedPureTensor q α) : Bool → WeightedPureTensor q α :=
  fun b => permuteWeightedPureTensor σ (K b)

/-- Each permutation commutes with a tensorized transition on pure tensors. -/
theorem permute_tensorized_transition_commute {q : ℕ} {α : Type*}
    (σ : Equiv.Perm (Fin q)) (T : α → α) (v : PureTensor q α) :
    permutePureTensor σ (tensorizedTransition T v) =
      tensorizedTransition T (permutePureTensor σ v) := by
  funext i
  simp [permutePureTensor, tensorizedTransition]

/-- Paper-facing permutation symmetry for the `q`-fold moment tensor power:
every coordinate permutation commutes with each tensorized transition, hence also with the
branchwise summed tensor collision kernel.
    thm:pom-momq-permutation-symmetry -/
theorem paper_pom_momq_permutation_symmetry {q : ℕ} {α : Type*}
    (G₀ G₁ : ℚ) (T₀ T₁ : α → α) :
    (∀ b : Bool, ∀ (σ : Equiv.Perm (Fin q)) (v : PureTensor q α),
      permutePureTensor σ (tensorTransitionFamily T₀ T₁ b v) =
        tensorTransitionFamily T₀ T₁ b (permutePureTensor σ v)) ∧
    ∀ (σ : Equiv.Perm (Fin q)) (v : PureTensor q α),
      permuteSummedTensorCollisionKernel σ (summedTensorCollisionKernel G₀ G₁ T₀ T₁ v) =
        summedTensorCollisionKernel G₀ G₁ T₀ T₁ (permutePureTensor σ v) := by
  refine ⟨?_, ?_⟩
  · intro b σ v
    cases b
    · simpa [tensorTransitionFamily] using
        (permute_tensorized_transition_commute σ (T := T₀) v)
    · simpa [tensorTransitionFamily] using
        (permute_tensorized_transition_commute σ (T := T₁) v)
  · intro σ v
    funext b
    cases b <;>
      simp [permuteSummedTensorCollisionKernel, summedTensorCollisionKernel,
        permuteWeightedPureTensor, permute_tensorized_transition_commute]

end Omega.POM
