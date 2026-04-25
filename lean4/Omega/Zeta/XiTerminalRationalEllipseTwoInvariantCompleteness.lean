import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The real `2 × 2` matrix obtained from a rational matrix by entrywise coercion. -/
def xi_terminal_rational_ellipse_two_invariant_completeness_realMatrix
    (A : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (A i j : ℝ)

/-- The determinant invariant `Δ₁(A) = (det A)^2`. -/
def xi_terminal_rational_ellipse_two_invariant_completeness_delta1
    (A : Matrix (Fin 2) (Fin 2) ℚ) : ℝ :=
  (xi_terminal_rational_ellipse_two_invariant_completeness_realMatrix A).det ^ 2

/-- The Gram-trace invariant `Δ₂(A) = tr(Aᵀ A)`. -/
def xi_terminal_rational_ellipse_two_invariant_completeness_delta2
    (A : Matrix (Fin 2) (Fin 2) ℚ) : ℝ :=
  Matrix.trace
    ((xi_terminal_rational_ellipse_two_invariant_completeness_realMatrix A).transpose *
      xi_terminal_rational_ellipse_two_invariant_completeness_realMatrix A)

/-- The quadratic discriminant `Δ₂(A)^2 - 4 Δ₁(A)`. -/
def xi_terminal_rational_ellipse_two_invariant_completeness_discriminant
    (A : Matrix (Fin 2) (Fin 2) ℚ) : ℝ :=
  xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A ^ 2 -
    4 * xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A

/-- The larger semiaxis-squared value recovered from `Δ₁` and `Δ₂`. -/
def xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus
    (A : Matrix (Fin 2) (Fin 2) ℚ) : ℝ :=
  (xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A +
      Real.sqrt (xi_terminal_rational_ellipse_two_invariant_completeness_discriminant A)) / 2

/-- The smaller semiaxis-squared value recovered from `Δ₁` and `Δ₂`. -/
def xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus
    (A : Matrix (Fin 2) (Fin 2) ℚ) : ℝ :=
  (xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A -
      Real.sqrt (xi_terminal_rational_ellipse_two_invariant_completeness_discriminant A)) / 2

/-- Euclidean congruence surrogate: equality of the recovered semiaxis-squared pair. -/
def xi_terminal_rational_ellipse_two_invariant_completeness_congruent
    (A B : Matrix (Fin 2) (Fin 2) ℚ) : Prop :=
  xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A =
      xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus B ∧
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A =
      xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus B

private theorem xi_terminal_rational_ellipse_two_invariant_completeness_delta2_explicit
    (A : Matrix (Fin 2) (Fin 2) ℚ) :
    xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A =
      (A 0 0 : ℝ) ^ 2 + (A 0 1 : ℝ) ^ 2 + (A 1 0 : ℝ) ^ 2 + (A 1 1 : ℝ) ^ 2 := by
  unfold xi_terminal_rational_ellipse_two_invariant_completeness_delta2
    xi_terminal_rational_ellipse_two_invariant_completeness_realMatrix
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem xi_terminal_rational_ellipse_two_invariant_completeness_delta1_explicit
    (A : Matrix (Fin 2) (Fin 2) ℚ) :
    xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A =
      (((A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) * (A 1 0 : ℝ))) ^ 2 := by
  simp [xi_terminal_rational_ellipse_two_invariant_completeness_delta1,
    xi_terminal_rational_ellipse_two_invariant_completeness_realMatrix, Matrix.det_fin_two]

private theorem
    xi_terminal_rational_ellipse_two_invariant_completeness_discriminant_nonneg
    (A : Matrix (Fin 2) (Fin 2) ℚ) :
    0 ≤ xi_terminal_rational_ellipse_two_invariant_completeness_discriminant A := by
  let a : ℝ := A 0 0
  let b : ℝ := A 0 1
  let c : ℝ := A 1 0
  let d : ℝ := A 1 1
  have hdisc :
      xi_terminal_rational_ellipse_two_invariant_completeness_discriminant A =
        ((a ^ 2 + c ^ 2) - (b ^ 2 + d ^ 2)) ^ 2 + 4 * (a * b + c * d) ^ 2 := by
    rw [xi_terminal_rational_ellipse_two_invariant_completeness_discriminant,
      xi_terminal_rational_ellipse_two_invariant_completeness_delta2_explicit,
      xi_terminal_rational_ellipse_two_invariant_completeness_delta1_explicit]
    simp [a, b, c, d]
    ring
  rw [hdisc]
  nlinarith [sq_nonneg ((a ^ 2 + c ^ 2) - (b ^ 2 + d ^ 2)), sq_nonneg (a * b + c * d)]

private theorem xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_sum
    (A : Matrix (Fin 2) (Fin 2) ℚ) :
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
      xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A =
        xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A := by
  simp [xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus,
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus]
  ring

private theorem xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_prod
    (A : Matrix (Fin 2) (Fin 2) ℚ) :
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A *
      xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A =
        xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A := by
  let d := xi_terminal_rational_ellipse_two_invariant_completeness_discriminant A
  have hnonneg :=
    xi_terminal_rational_ellipse_two_invariant_completeness_discriminant_nonneg A
  have hsqrt :
      Real.sqrt d ^ 2 = d := by
    simpa [d] using Real.sq_sqrt hnonneg
  calc
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A *
        xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A =
      (xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A ^ 2 - d) / 4 := by
        unfold xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus
          xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus
        rw [← hsqrt]
        ring
    _ = xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A := by
        dsimp [d]
        unfold xi_terminal_rational_ellipse_two_invariant_completeness_discriminant
        ring

private theorem xi_terminal_rational_ellipse_two_invariant_completeness_plus_is_root
    (A : Matrix (Fin 2) (Fin 2) ℚ) :
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A ^ 2 -
      xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A *
        xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
          xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A = 0 := by
  calc
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A ^ 2 -
        xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A *
          xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
            xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A =
      xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A ^ 2 -
        (xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
          xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A) *
            xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
              xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A *
                xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A := by
                  rw [xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_sum,
                    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_prod]
    _ = 0 := by ring

private theorem xi_terminal_rational_ellipse_two_invariant_completeness_minus_is_root
    (A : Matrix (Fin 2) (Fin 2) ℚ) :
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A ^ 2 -
      xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A *
        xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A +
          xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A = 0 := by
  calc
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A ^ 2 -
        xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A *
          xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A +
            xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A =
      xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A ^ 2 -
        (xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
          xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A) *
            xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A +
              xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A *
                xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A := by
                  rw [xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_sum,
                    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_prod]
    _ = 0 := by ring

def xi_terminal_rational_ellipse_two_invariant_completeness_statement : Prop :=
  (∀ A : Matrix (Fin 2) (Fin 2) ℚ,
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A ^ 2 -
      xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A *
        xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
          xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A = 0 ∧
    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A ^ 2 -
      xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A *
        xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A +
          xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A = 0) ∧
    ∀ A B : Matrix (Fin 2) (Fin 2) ℚ, A.det ≠ 0 → B.det ≠ 0 →
      (xi_terminal_rational_ellipse_two_invariant_completeness_congruent A B ↔
        xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A =
            xi_terminal_rational_ellipse_two_invariant_completeness_delta1 B ∧
          xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A =
            xi_terminal_rational_ellipse_two_invariant_completeness_delta2 B)

/-- Paper label: `thm:xi-terminal-rational-ellipse-two-invariant-completeness`. The two invariants
`Δ₁ = (det A)^2` and `Δ₂ = tr(Aᵀ A)` recover the semiaxis-squared pair as the two roots of the
quadratic `t^2 - Δ₂ t + Δ₁`, so equality of the invariant pair is equivalent to equality of the
ellipse data. -/
theorem paper_xi_terminal_rational_ellipse_two_invariant_completeness :
    xi_terminal_rational_ellipse_two_invariant_completeness_statement := by
  refine ⟨?_, ?_⟩
  · intro A
    exact ⟨xi_terminal_rational_ellipse_two_invariant_completeness_plus_is_root A,
      xi_terminal_rational_ellipse_two_invariant_completeness_minus_is_root A⟩
  · intro A B hA hB
    constructor
    · rintro ⟨hplus, hminus⟩
      refine ⟨?_, ?_⟩
      · calc
          xi_terminal_rational_ellipse_two_invariant_completeness_delta1 A =
              xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A *
                xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A := by
                  symm
                  exact
                    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_prod A
          _ =
              xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus B *
                xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus B := by
                  rw [hplus, hminus]
          _ =
              xi_terminal_rational_ellipse_two_invariant_completeness_delta1 B := by
                  exact
                    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_prod B
      · calc
          xi_terminal_rational_ellipse_two_invariant_completeness_delta2 A =
              xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus A +
                xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus A := by
                  symm
                  exact
                    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_sum A
          _ =
              xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus B +
                xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus B := by
                  rw [hplus, hminus]
          _ =
              xi_terminal_rational_ellipse_two_invariant_completeness_delta2 B := by
                  exact
                    xi_terminal_rational_ellipse_two_invariant_completeness_semiaxis_sum B
    · rintro ⟨hΔ1, hΔ2⟩
      let _ := hA
      let _ := hB
      constructor <;>
        simp [xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqPlus,
          xi_terminal_rational_ellipse_two_invariant_completeness_semiaxisSqMinus,
          xi_terminal_rational_ellipse_two_invariant_completeness_discriminant, hΔ1, hΔ2]

end
end Omega.Zeta
