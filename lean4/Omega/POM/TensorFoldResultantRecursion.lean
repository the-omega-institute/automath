import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

/-- Concrete two-factor finite exponential-sum data for the tensor Hadamard pole law.

The fields are numerical data and concrete hypotheses: nonzero coefficients and roots,
rootwise no-collision for tensor products, and chosen maximizers for the two spectral radii. -/
structure pom_tensor_hadamard_pole_law_pressure_additivity_data where
  leftSize : ℕ
  rightSize : ℕ
  c₁ : Fin leftSize → ℝ
  α : Fin leftSize → ℝ
  c₂ : Fin rightSize → ℝ
  β : Fin rightSize → ℝ
  leftMax : Fin leftSize
  rightMax : Fin rightSize
  leftCoeff_ne_zero : ∀ i, c₁ i ≠ 0
  rightCoeff_ne_zero : ∀ j, c₂ j ≠ 0
  leftRoot_ne_zero : ∀ i, α i ≠ 0
  rightRoot_ne_zero : ∀ j, β j ≠ 0
  productRoot_injective : Function.Injective (fun p : Fin leftSize × Fin rightSize =>
    α p.1 * β p.2)
  left_abs_le : ∀ i, |α i| ≤ |α leftMax|
  right_abs_le : ∀ j, |β j| ≤ |β rightMax|

namespace pom_tensor_hadamard_pole_law_pressure_additivity_data

/-- The left finite exponential-sum factor. -/
def leftSeq (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) (m : ℕ) : ℝ :=
  ∑ i, D.c₁ i * D.α i ^ m

/-- The right finite exponential-sum factor. -/
def rightSeq (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) (m : ℕ) : ℝ :=
  ∑ j, D.c₂ j * D.β j ^ m

/-- The Hadamard product coefficient sequence. -/
def productSeq (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) (m : ℕ) : ℝ :=
  D.leftSeq m * D.rightSeq m

/-- Tensor coefficients indexed by a pair of modes. -/
def tensorCoefficient
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data)
    (p : Fin D.leftSize × Fin D.rightSize) : ℝ :=
  D.c₁ p.1 * D.c₂ p.2

/-- Tensor roots indexed by a pair of modes. -/
def productRoot
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data)
    (p : Fin D.leftSize × Fin D.rightSize) : ℝ :=
  D.α p.1 * D.β p.2

/-- The finite exponential-sum expansion after Hadamard multiplication. -/
def expandedSeq (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) (m : ℕ) : ℝ :=
  ∑ p : Fin D.leftSize × Fin D.rightSize, D.tensorCoefficient p * D.productRoot p ^ m

/-- The chosen spectral radius of the left factor. -/
def leftSpectralRadius
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : ℝ :=
  |D.α D.leftMax|

/-- The chosen spectral radius of the right factor. -/
def rightSpectralRadius
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : ℝ :=
  |D.β D.rightMax|

/-- The chosen spectral radius of the tensor Hadamard product. -/
def productSpectralRadius
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : ℝ :=
  |D.productRoot (D.leftMax, D.rightMax)|

/-- The left pressure. -/
noncomputable def leftPressure
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : ℝ :=
  Real.log D.leftSpectralRadius

/-- The right pressure. -/
noncomputable def rightPressure
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : ℝ :=
  Real.log D.rightSpectralRadius

/-- The tensor Hadamard pressure. -/
noncomputable def productPressure
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : ℝ :=
  Real.log D.productSpectralRadius

/-- The partial-fraction numerator/root package is exactly the finite product-index expansion. -/
def partialFractionExpansion
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : Prop :=
  ∀ m : ℕ, D.productSeq m = D.expandedSeq m

/-- Nonzero tensor coefficients and no repeated tensor roots give only simple active poles. -/
def singlePoleLaw
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : Prop :=
  (∀ p : Fin D.leftSize × Fin D.rightSize, D.tensorCoefficient p ≠ 0) ∧
    Function.Injective D.productRoot

/-- Taking inverses gives exactly the pole list, with no collisions and no zero roots. -/
def poleSetExact
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : Prop :=
  Function.Injective (fun p : Fin D.leftSize × Fin D.rightSize => (D.productRoot p)⁻¹) ∧
    ∀ p : Fin D.leftSize × Fin D.rightSize, D.productRoot p ≠ 0

/-- The tensor spectral radius is the product of the two factor radii, hence pressure adds. -/
def pressureAdditive
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) : Prop :=
  (∀ p : Fin D.leftSize × Fin D.rightSize,
      |D.productRoot p| ≤ D.productSpectralRadius) ∧
    D.productPressure = D.leftPressure + D.rightPressure

end pom_tensor_hadamard_pole_law_pressure_additivity_data

open pom_tensor_hadamard_pole_law_pressure_additivity_data

/-- Paper label:
`thm:pom-tensor-hadamard-pole-law-pressure-additivity`. -/
theorem paper_pom_tensor_hadamard_pole_law_pressure_additivity
    (D : pom_tensor_hadamard_pole_law_pressure_additivity_data) :
    D.partialFractionExpansion ∧ D.singlePoleLaw ∧ D.poleSetExact ∧
      D.pressureAdditive := by
  constructor
  · intro m
    calc
      D.productSeq m
          = ∑ j, ∑ i, (D.c₁ i * D.α i ^ m) * (D.c₂ j * D.β j ^ m) := by
              simp [pom_tensor_hadamard_pole_law_pressure_additivity_data.productSeq,
                pom_tensor_hadamard_pole_law_pressure_additivity_data.leftSeq,
                pom_tensor_hadamard_pole_law_pressure_additivity_data.rightSeq,
                Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i, ∑ j, (D.c₁ i * D.α i ^ m) * (D.c₂ j * D.β j ^ m) := by
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, (D.c₁ i * D.c₂ j) * (D.α i * D.β j) ^ m := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [mul_pow]
            ring
      _ = D.expandedSeq m := by
            rw [pom_tensor_hadamard_pole_law_pressure_additivity_data.expandedSeq,
              Fintype.sum_prod_type]
            rfl
  · constructor
    · constructor
      · intro p
        exact mul_ne_zero (D.leftCoeff_ne_zero p.1) (D.rightCoeff_ne_zero p.2)
      · exact D.productRoot_injective
    · constructor
      · constructor
        · intro p q hpq
          apply D.productRoot_injective
          simpa using congrArg Inv.inv hpq
        · intro p
          exact mul_ne_zero (D.leftRoot_ne_zero p.1) (D.rightRoot_ne_zero p.2)
      · constructor
        · intro p
          calc
            |D.productRoot p| = |D.α p.1| * |D.β p.2| := by
                simp [
                  pom_tensor_hadamard_pole_law_pressure_additivity_data.productRoot,
                  abs_mul]
            _ ≤ D.leftSpectralRadius * D.rightSpectralRadius := by
                exact mul_le_mul (D.left_abs_le p.1) (D.right_abs_le p.2)
                  (abs_nonneg _) (abs_nonneg _)
            _ = D.productSpectralRadius := by
                rw [
                  pom_tensor_hadamard_pole_law_pressure_additivity_data.leftSpectralRadius,
                  pom_tensor_hadamard_pole_law_pressure_additivity_data.rightSpectralRadius,
                  pom_tensor_hadamard_pole_law_pressure_additivity_data.productSpectralRadius,
                  pom_tensor_hadamard_pole_law_pressure_additivity_data.productRoot,
                  abs_mul]
        · have hleft_pos : 0 < D.leftSpectralRadius := by
            rw [pom_tensor_hadamard_pole_law_pressure_additivity_data.leftSpectralRadius]
            exact abs_pos.mpr (D.leftRoot_ne_zero D.leftMax)
          have hright_pos : 0 < D.rightSpectralRadius := by
            rw [pom_tensor_hadamard_pole_law_pressure_additivity_data.rightSpectralRadius]
            exact abs_pos.mpr (D.rightRoot_ne_zero D.rightMax)
          have hprod :
              D.productSpectralRadius = D.leftSpectralRadius * D.rightSpectralRadius := by
            rw [
              pom_tensor_hadamard_pole_law_pressure_additivity_data.leftSpectralRadius,
              pom_tensor_hadamard_pole_law_pressure_additivity_data.rightSpectralRadius,
              pom_tensor_hadamard_pole_law_pressure_additivity_data.productSpectralRadius,
              pom_tensor_hadamard_pole_law_pressure_additivity_data.productRoot,
              abs_mul]
          calc
            D.productPressure = Real.log D.productSpectralRadius := rfl
            _ = Real.log (D.leftSpectralRadius * D.rightSpectralRadius) := by rw [hprod]
            _ = Real.log D.leftSpectralRadius + Real.log D.rightSpectralRadius := by
                exact Real.log_mul hleft_pos.ne' hright_pos.ne'
            _ = D.leftPressure + D.rightPressure := rfl

end Omega.POM
