import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped Matrix

/-- Concrete seed for the standard `S₃` realization computation. -/
abbrev xi_s3_closure_standard_isotypic_explicit_r3_realization_data := Unit

/-- Three-coordinate integral realization of the permutation representation. -/
abbrev xi_s3_closure_standard_isotypic_explicit_r3_realization_triple :=
  Fin 3 → ℤ

/-- The rank-two standard summand is the zero-sum plane. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard
    (x : xi_s3_closure_standard_isotypic_explicit_r3_realization_triple) : Prop :=
  x 0 + x 1 + x 2 = 0

/-- First standard basis vector `(1,-1,0)`. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_v1 :
    xi_s3_closure_standard_isotypic_explicit_r3_realization_triple :=
  ![1, -1, 0]

/-- Second standard basis vector `(0,1,-1)`. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_v2 :
    xi_s3_closure_standard_isotypic_explicit_r3_realization_triple :=
  ![0, 1, -1]

/-- Linear combination in the basis `v₁,v₂`. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_basisCombination
    (c : Fin 2 → ℤ) : xi_s3_closure_standard_isotypic_explicit_r3_realization_triple :=
  fun i =>
    c 0 * xi_s3_closure_standard_isotypic_explicit_r3_realization_v1 i +
      c 1 * xi_s3_closure_standard_isotypic_explicit_r3_realization_v2 i

/-- The `(123)` action under the convention `σ · P = P ∘ σ⁻¹`. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleTriple
    (x : xi_s3_closure_standard_isotypic_explicit_r3_realization_triple) :
    xi_s3_closure_standard_isotypic_explicit_r3_realization_triple :=
  ![x 2, x 0, x 1]

/-- The `(12)` action under the convention `σ · P = P ∘ σ⁻¹`. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionTriple
    (x : xi_s3_closure_standard_isotypic_explicit_r3_realization_triple) :
    xi_s3_closure_standard_isotypic_explicit_r3_realization_triple :=
  ![x 1, x 0, x 2]

/-- Matrix of `(123)` on the basis `v₁,v₂`. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 0 else -1
    else
      if j = 0 then 1 else -1

/-- Matrix of `(12)` on the basis `v₁,v₂`. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionMatrix :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j =>
    if i = 0 then
      if j = 0 then -1 else 1
    else
      if j = 0 then 0 else 1

/-- Concrete conclusion: the matrices are the advertised standard representation matrices. -/
def xi_s3_closure_standard_isotypic_explicit_r3_realization_conclusion
    (_D : xi_s3_closure_standard_isotypic_explicit_r3_realization_data) : Prop :=
  xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard
      xi_s3_closure_standard_isotypic_explicit_r3_realization_v1 ∧
    xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard
      xi_s3_closure_standard_isotypic_explicit_r3_realization_v2 ∧
    (∀ x,
      xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard x →
        xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard
          (xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleTriple x)) ∧
    (∀ x,
      xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard x →
        xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard
          (xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionTriple x)) ∧
    (∀ c,
      xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleTriple
          (xi_s3_closure_standard_isotypic_explicit_r3_realization_basisCombination c) =
        xi_s3_closure_standard_isotypic_explicit_r3_realization_basisCombination
          (xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix.mulVec c)) ∧
    (∀ c,
      xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionTriple
          (xi_s3_closure_standard_isotypic_explicit_r3_realization_basisCombination c) =
        xi_s3_closure_standard_isotypic_explicit_r3_realization_basisCombination
          (xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionMatrix.mulVec c)) ∧
    xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix *
          xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix +
        xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix + 1 =
      0 ∧
    (∀ c : Fin 2 → ℤ,
      xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix.mulVec c = c →
        c = 0)

/-- Paper label: `prop:xi-s3-closure-standard-isotypic-explicit-r3-realization`. -/
theorem paper_xi_s3_closure_standard_isotypic_explicit_r3_realization
    (D : xi_s3_closure_standard_isotypic_explicit_r3_realization_data) :
    xi_s3_closure_standard_isotypic_explicit_r3_realization_conclusion D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (1 : ℤ) + -1 + 0 = 0
    norm_num
  · change (0 : ℤ) + 1 + -1 = 0
    norm_num
  · intro x hx
    dsimp [xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard,
      xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleTriple] at hx ⊢
    omega
  · intro x hx
    dsimp [xi_s3_closure_standard_isotypic_explicit_r3_realization_inStandard,
      xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionTriple] at hx ⊢
    omega
  · intro c
    funext i
    fin_cases i <;>
      simp [xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleTriple,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_basisCombination,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_v1,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_v2, Matrix.mulVec];
      ring
  · intro c
    funext i
    fin_cases i <;>
      simp [xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionTriple,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_basisCombination,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_transpositionMatrix,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_v1,
        xi_s3_closure_standard_isotypic_explicit_r3_realization_v2, Matrix.mulVec]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix,
        Matrix.mul_apply, Fin.sum_univ_two]
  · intro c hc
    funext i
    have h0 := congr_fun hc 0
    have h1 := congr_fun hc 1
    fin_cases i <;>
      simp [xi_s3_closure_standard_isotypic_explicit_r3_realization_cycleMatrix,
        Matrix.mulVec] at h0 h1 ⊢ <;>
      omega

end Omega.Zeta
