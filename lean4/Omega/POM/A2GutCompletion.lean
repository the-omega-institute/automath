import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Tactic

namespace Omega.POM

open Matrix

noncomputable section

/-- The explicit `A₂` collision kernel. -/
def pom_a2_gut_completion_A2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1;
    0, 1, 1;
    2, 1, 1]

/-- The rank-one unified channel. -/
def pom_a2_gut_completion_U : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1;
    0, 0, 1;
    0, 0, 1]

/-- The residual exchange term `R = A₂ - U`. -/
def pom_a2_gut_completion_R : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0;
    0, 1, 0;
    2, 1, 0]

/-- The explicit left factor in the rank-two exchange decomposition. -/
def pom_a2_gut_completion_B : Matrix (Fin 3) (Fin 2) ℝ :=
  !![0, 0;
    0, 1;
    1, 0]

/-- The explicit right factor in the rank-two exchange decomposition. -/
def pom_a2_gut_completion_C : Matrix (Fin 2) (Fin 3) ℝ :=
  !![2, 1, 0;
    0, 1, 0]

/-- The column vector spanning the unified channel. -/
def pom_a2_gut_completion_u : Fin 3 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1

/-- The row vector spanning the unified channel. -/
def pom_a2_gut_completion_v : Fin 3 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1

/-- The explicit `5 × 5` bookkeeping completion. -/
def pom_a2_gut_completion_AGUT : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 0, 1, 0, 0;
    0, 0, 1, 0, 1;
    0, 0, 1, 1, 0;
    2, 1, 0, 0, 0;
    0, 1, 0, 0, 0]

lemma pom_a2_gut_completion_U_eq_vecMulVec :
    pom_a2_gut_completion_U =
      Matrix.vecMulVec pom_a2_gut_completion_u pom_a2_gut_completion_v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pom_a2_gut_completion_U, pom_a2_gut_completion_u, pom_a2_gut_completion_v,
      Matrix.vecMulVec]

lemma pom_a2_gut_completion_u_ne_zero : pom_a2_gut_completion_u ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : Fin 3 → ℝ => f 0) h
  norm_num [pom_a2_gut_completion_u] at h0

lemma pom_a2_gut_completion_v_ne_zero : pom_a2_gut_completion_v ≠ 0 := by
  intro h
  have h2 := congrArg (fun f : Fin 3 → ℝ => f 2) h
  norm_num [pom_a2_gut_completion_v] at h2

lemma pom_a2_gut_completion_R_eq_BC :
    pom_a2_gut_completion_R = pom_a2_gut_completion_B * pom_a2_gut_completion_C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pom_a2_gut_completion_R, pom_a2_gut_completion_B, pom_a2_gut_completion_C,
      Matrix.mul_apply, Fin.sum_univ_two]

lemma pom_a2_gut_completion_A2_eq_U_add_BC :
    pom_a2_gut_completion_A2 =
      pom_a2_gut_completion_U + pom_a2_gut_completion_B * pom_a2_gut_completion_C := by
  rw [← pom_a2_gut_completion_R_eq_BC]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pom_a2_gut_completion_A2, pom_a2_gut_completion_U, pom_a2_gut_completion_R]

lemma pom_a2_gut_completion_R_col0_ne_zero : pom_a2_gut_completion_R.col 0 ≠ 0 := by
  intro h
  have h2 := congrArg (fun f : Fin 3 → ℝ => f 2) h
  have : (2 : ℝ) = 0 := by
    simpa [pom_a2_gut_completion_R, Matrix.col] using h2
  norm_num at this

lemma pom_a2_gut_completion_R_col1_not_smul_col0 :
    ¬ ∃ a : ℝ, pom_a2_gut_completion_R.col 1 = a • pom_a2_gut_completion_R.col 0 := by
  rintro ⟨a, ha⟩
  have h1 := congrArg (fun f : Fin 3 → ℝ => f 1) ha
  norm_num [pom_a2_gut_completion_R, Matrix.col] at h1

/-- Paper label: `prop:pom-a2-gut-completion`.  The explicit `A₂` kernel splits as a nonzero
rank-one outer product plus a rank-two exchange term with a two-state factorization, and no
factorization through fewer than two auxiliary states can reproduce the exchange term. -/
theorem paper_pom_a2_gut_completion :
    pom_a2_gut_completion_U =
        Matrix.vecMulVec pom_a2_gut_completion_u pom_a2_gut_completion_v ∧
      pom_a2_gut_completion_u ≠ 0 ∧
      pom_a2_gut_completion_v ≠ 0 ∧
      pom_a2_gut_completion_R = pom_a2_gut_completion_B * pom_a2_gut_completion_C ∧
      pom_a2_gut_completion_A2 =
        pom_a2_gut_completion_U + pom_a2_gut_completion_B * pom_a2_gut_completion_C ∧
      pom_a2_gut_completion_R.col 0 ≠ 0 ∧
      (¬ ∃ a : ℝ, pom_a2_gut_completion_R.col 1 = a • pom_a2_gut_completion_R.col 0) ∧
      ∀ {k : ℕ} (Btilde : Matrix (Fin 3) (Fin k) ℝ) (Ctilde : Matrix (Fin k) (Fin 3) ℝ),
        pom_a2_gut_completion_R = Btilde * Ctilde → 2 ≤ k := by
  refine ⟨pom_a2_gut_completion_U_eq_vecMulVec, pom_a2_gut_completion_u_ne_zero,
    pom_a2_gut_completion_v_ne_zero, pom_a2_gut_completion_R_eq_BC,
    pom_a2_gut_completion_A2_eq_U_add_BC, pom_a2_gut_completion_R_col0_ne_zero,
    pom_a2_gut_completion_R_col1_not_smul_col0, ?_⟩
  intro k Btilde Ctilde hfac
  by_cases hk : 2 ≤ k
  · exact hk
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · have h20 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 0) hfac
      simp [pom_a2_gut_completion_R, Matrix.mul_apply] at h20
    · let bcol : Fin 3 → ℝ := Btilde.col 0
      have hcol0 :
          pom_a2_gut_completion_R.col 0 = Ctilde 0 0 • bcol := by
        ext i
        rw [hfac]
        simp [bcol, Matrix.col, Matrix.mul_apply]
        ring
      have hcol1 :
          pom_a2_gut_completion_R.col 1 = Ctilde 0 1 • bcol := by
        ext i
        rw [hfac]
        simp [bcol, Matrix.col, Matrix.mul_apply]
        ring
      by_cases hc00 : Ctilde 0 0 = 0
      · have hzero : pom_a2_gut_completion_R.col 0 = 0 := by
          simpa [hcol0, hc00, bcol]
        exfalso
        exact pom_a2_gut_completion_R_col0_ne_zero hzero
      · have hrow0 : Ctilde 0 0 * bcol 1 = 0 := by
          have hrow1_0 := congrArg (fun f : Fin 3 → ℝ => f 1) hcol0
          simpa [pom_a2_gut_completion_R, Matrix.col, bcol] using hrow1_0
        have hb1 : bcol 1 = 0 := by
          exact (mul_eq_zero.mp hrow0).resolve_left hc00
        have hrow1 : (1 : ℝ) = Ctilde 0 1 * bcol 1 := by
          have hrow1_1 := congrArg (fun f : Fin 3 → ℝ => f 1) hcol1
          simpa [pom_a2_gut_completion_R, Matrix.col, bcol] using hrow1_1
        exfalso
        simp [hb1] at hrow1

end

end Omega.POM
