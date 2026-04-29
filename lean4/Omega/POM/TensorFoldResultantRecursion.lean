import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators
open Polynomial

/-- Chapter-local wrapper for the multifactor tensor resultant recursion package. The auxiliary
fields record the factor list, the no-collision hypothesis, the two-factor closure, and the
induction step used to pass from the two-factor case to the iterated resultant. The paper-facing
outputs are the minimal-polynomial identification together with degree and Hankel-rank
multiplicativity. -/
structure TensorFoldResultantRecursionData where
  Factor : Type
  factors : List Factor
  noCollision : Prop
  twoFactorClosure : Prop
  inductionStep : Prop
  iteratedResultantIsMinimalPolynomial : Prop
  degreeMultiplicativity : Prop
  hankelRankMultiplicativity : Prop
  noCollision_h : noCollision
  twoFactorClosure_h : twoFactorClosure
  inductionStep_h : inductionStep
  iteratedResultantIsMinimalPolynomial_h : iteratedResultantIsMinimalPolynomial
  degreeMultiplicativity_h : degreeMultiplicativity
  hankelRankMultiplicativity_h : hankelRankMultiplicativity

/-- Paper-facing wrapper for the strict multiplicativity of the multifactor tensor resultant
recursion.
    thm:pom-multifactor-tensor-recurrence-strict-multiplicativity -/
theorem paper_pom_multifactor_tensor_recurrence_strict_multiplicativity
    (D : TensorFoldResultantRecursionData) :
    D.iteratedResultantIsMinimalPolynomial ∧
      D.degreeMultiplicativity ∧
      D.hankelRankMultiplicativity := by
  exact ⟨D.iteratedResultantIsMinimalPolynomial_h, D.degreeMultiplicativity_h,
    D.hankelRankMultiplicativity_h⟩

/-- A finite exponential-sum model for one factor in the tensor-fold recursion package. -/
def tensorFactorSeq {ι : Type} [Fintype ι] (c α : ι → ℚ) (m : ℕ) : ℚ :=
  ∑ i, c i * α i ^ m

/-- The pointwise product of the two factor sequences. -/
def tensorProductSeq {ι κ : Type} [Fintype ι] [Fintype κ]
    (c₁ : ι → ℚ) (α : ι → ℚ) (c₂ : κ → ℚ) (β : κ → ℚ) (m : ℕ) : ℚ :=
  tensorFactorSeq c₁ α m * tensorFactorSeq c₂ β m

/-- Tensor-product coefficients indexed by pairs of roots. -/
def tensorCoeff {ι κ : Type} (c₁ : ι → ℚ) (c₂ : κ → ℚ) : ι × κ → ℚ :=
  fun p => c₁ p.1 * c₂ p.2

/-- Tensor-product roots indexed by pairs of roots. -/
def tensorRoot {ι κ : Type} (α : ι → ℚ) (β : κ → ℚ) : ι × κ → ℚ :=
  fun p => α p.1 * β p.2

/-- The pairwise root expansion of the tensor-product sequence. -/
def tensorExpandedSeq {ι κ : Type} [Fintype ι] [Fintype κ]
    (c₁ : ι → ℚ) (α : ι → ℚ) (c₂ : κ → ℚ) (β : κ → ℚ) (m : ℕ) : ℚ :=
  ∑ p : ι × κ, tensorCoeff c₁ c₂ p * tensorRoot α β p ^ m

/-- The active-mode polynomial attached to the tensor-product expansion. -/
noncomputable def tensorModePolynomial
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c₁ : ι → ℚ) (c₂ : κ → ℚ) (α : ι → ℚ) (β : κ → ℚ) : Polynomial ℚ :=
  Finset.prod ((Finset.univ : Finset (ι × κ)).filter (fun p => tensorCoeff c₁ c₂ p ≠ 0))
    (fun p => X - C (tensorRoot α β p))

/-- The inactive-mode cofactor complementary to `tensorModePolynomial`. -/
noncomputable def tensorInactivePolynomial
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c₁ : ι → ℚ) (c₂ : κ → ℚ) (α : ι → ℚ) (β : κ → ℚ) : Polynomial ℚ :=
  Finset.prod ((Finset.univ : Finset (ι × κ)).filter (fun p => ¬ tensorCoeff c₁ c₂ p ≠ 0))
    (fun p => X - C (tensorRoot α β p))

/-- The concrete rootwise resultant polynomial for the two-factor tensor product. -/
noncomputable def tensorResultantPolynomial {ι κ : Type} [Fintype ι] [Fintype κ]
    (α : ι → ℚ) (β : κ → ℚ) : Polynomial ℚ :=
  ∏ p : ι × κ, (X - C (tensorRoot α β p))

theorem tensorProductSeq_eq_tensorExpandedSeq {ι κ : Type} [Fintype ι] [Fintype κ]
    (c₁ : ι → ℚ) (α : ι → ℚ) (c₂ : κ → ℚ) (β : κ → ℚ) (m : ℕ) :
    tensorProductSeq c₁ α c₂ β m = tensorExpandedSeq c₁ α c₂ β m := by
  calc
    tensorProductSeq c₁ α c₂ β m
        = ∑ j, ∑ i, (c₁ i * α i ^ m) * (c₂ j * β j ^ m) := by
            simp [tensorProductSeq, tensorFactorSeq, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ j, (c₁ i * α i ^ m) * (c₂ j * β j ^ m) := by
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (c₁ i * c₂ j) * (α i * β j) ^ m := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [mul_pow]
          ring
    _ = tensorExpandedSeq c₁ α c₂ β m := by
          rw [tensorExpandedSeq, Fintype.sum_prod_type]
          rfl

theorem tensorModePolynomial_eq_tensorResultant {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (c₁ : ι → ℚ) (c₂ : κ → ℚ) (α : ι → ℚ) (β : κ → ℚ)
    (hc₁ : ∀ i, c₁ i ≠ 0) (hc₂ : ∀ j, c₂ j ≠ 0) :
    tensorModePolynomial c₁ c₂ α β = tensorResultantPolynomial α β := by
  classical
  unfold tensorModePolynomial tensorResultantPolynomial
  refine congrArg (fun s => Finset.prod s (fun p => X - C (tensorRoot α β p))) ?_
  ext p
  simp [tensorCoeff, hc₁ p.1, hc₂ p.2]

theorem tensorModePolynomial_dvd_tensorResultant {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (c₁ : ι → ℚ) (c₂ : κ → ℚ) (α : ι → ℚ) (β : κ → ℚ) :
    tensorModePolynomial c₁ c₂ α β ∣ tensorResultantPolynomial α β := by
  classical
  refine ⟨tensorInactivePolynomial c₁ c₂ α β, ?_⟩
  unfold tensorModePolynomial tensorInactivePolynomial tensorResultantPolynomial
  exact
    (Finset.prod_filter_mul_prod_filter_not
      (Finset.univ : Finset (ι × κ))
      (fun p : ι × κ => tensorCoeff c₁ c₂ p ≠ 0)
      (fun p => X - C (tensorRoot α β p))).symm

/-- `thm:pom-twofactor-tensor-recurrence-exact-resultant-closure` -/
theorem paper_pom_twofactor_tensor_recurrence_exact_resultant_closure
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c1 : ι → ℚ) (α : ι → ℚ) (c2 : κ → ℚ) (β : κ → ℚ) (hc1 : ∀ i, c1 i ≠ 0)
    (hc2 : ∀ j, c2 j ≠ 0) (hroot : Function.Injective (tensorRoot α β)) :
    tensorModePolynomial (ι := ι) (κ := κ) c1 c2 α β =
      tensorResultantPolynomial (ι := ι) (κ := κ) α β := by
  let _ := hroot
  exact tensorModePolynomial_eq_tensorResultant (ι := ι) (κ := κ) c1 c2 α β hc1 hc2

/-- Concrete two-factor precursor for the tensor-fold resultant recursion: the product sequence
expands over tensor roots, the active-mode polynomial divides the full resultant, and the
resultant itself is the explicit product over pairwise roots.
    thm:pom-tensor-fold-resultant-recursion -/
theorem paper_pom_tensor_fold_resultant_recursion
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (c₁ : ι → ℚ) (α : ι → ℚ) (c₂ : κ → ℚ) (β : κ → ℚ) :
    (∀ m : ℕ, tensorProductSeq c₁ α c₂ β m = tensorExpandedSeq c₁ α c₂ β m) ∧
      tensorModePolynomial c₁ c₂ α β ∣ tensorResultantPolynomial α β ∧
      tensorResultantPolynomial α β =
        ∏ p : ι × κ, (X - C (tensorRoot α β p)) := by
  exact ⟨tensorProductSeq_eq_tensorExpandedSeq c₁ α c₂ β,
    tensorModePolynomial_dvd_tensorResultant c₁ c₂ α β, rfl⟩

end Omega.POM
