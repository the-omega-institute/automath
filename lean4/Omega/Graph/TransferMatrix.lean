import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Core.Fib

namespace Omega.Graph

/-- The 2x2 adjacency (transfer) matrix of the golden-mean shift:
    A = [[1,1],[1,0]], encoding allowed transitions in the No11 constraint.
    def:golden-mean-adjacency-matrix -/
def goldenMeanAdjacency : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 0]

/-- Entry (0,0) = 1: transition 0 → 0 is allowed.
    prop:golden-mean-adjacency-entry-00 -/
theorem goldenMeanAdjacency_entry_00 : goldenMeanAdjacency 0 0 = 1 := by native_decide

/-- Entry (0,1) = 1: transition 0 → 1 is allowed.
    prop:golden-mean-adjacency-entry-01 -/
theorem goldenMeanAdjacency_entry_01 : goldenMeanAdjacency 0 1 = 1 := by native_decide

/-- Entry (1,0) = 1: transition 1 → 0 is allowed.
    prop:golden-mean-adjacency-entry-10 -/
theorem goldenMeanAdjacency_entry_10 : goldenMeanAdjacency 1 0 = 1 := by native_decide

/-- Entry (1,1) = 0: transition 1 → 1 is forbidden (No11 constraint).
    prop:golden-mean-adjacency-entry-11 -/
theorem goldenMeanAdjacency_entry_11 : goldenMeanAdjacency 1 1 = 0 := by native_decide

/-- Concrete Cayley-Hamilton identity: A² = A + I for the golden-mean adjacency matrix.
    thm:fold-suite-item3-cayley-hamilton -/
theorem goldenMeanAdjacency_sq :
    goldenMeanAdjacency ^ 2 = goldenMeanAdjacency + 1 := by native_decide

/-- Trace of the golden-mean adjacency matrix is 1.
    prop:golden-mean-adjacency-trace -/
theorem goldenMeanAdjacency_trace : goldenMeanAdjacency.trace = 1 := by native_decide

/-- Determinant of the golden-mean adjacency matrix is -1.
    prop:golden-mean-adjacency-det -/
theorem goldenMeanAdjacency_det : goldenMeanAdjacency.det = -1 := by native_decide

/-! ### Transfer matrix and Fibonacci numbers -/

/-- A^(m+2) = A^(m+1) + A^m (matrix Fibonacci recurrence from A² = A + I).
    cor:folding-stable-syntax-entropy-logqdim-matrix-recurrence -/
theorem goldenMeanAdjacency_pow_add_two (m : Nat) :
    goldenMeanAdjacency ^ (m + 2) =
      goldenMeanAdjacency ^ (m + 1) + goldenMeanAdjacency ^ m := by
  have : goldenMeanAdjacency ^ (m + 2) = goldenMeanAdjacency ^ m * goldenMeanAdjacency ^ 2 := by
    rw [← pow_add]
  rw [this, goldenMeanAdjacency_sq, mul_add, mul_one, pow_succ]

/-- Row-sum of A^m equals Nat.fib(m+2) (cast to ℤ).
    cor:folding-stable-syntax-entropy-logqdim-row-sum -/
theorem goldenMeanAdjacency_row_sum :
    ∀ m : Nat, (goldenMeanAdjacency ^ m) 0 0 + (goldenMeanAdjacency ^ m) 0 1 =
      (Nat.fib (m + 2) : ℤ)
  | 0 => by native_decide
  | 1 => by native_decide
  | m + 2 => by
    have hRec := goldenMeanAdjacency_pow_add_two m
    have ih1 := goldenMeanAdjacency_row_sum (m + 1)
    have ih0 := goldenMeanAdjacency_row_sum m
    simp only [hRec, Matrix.add_apply]
    rw [show (goldenMeanAdjacency ^ (m + 1)) 0 0 + (goldenMeanAdjacency ^ m) 0 0 +
        ((goldenMeanAdjacency ^ (m + 1)) 0 1 + (goldenMeanAdjacency ^ m) 0 1) =
        ((goldenMeanAdjacency ^ (m + 1)) 0 0 + (goldenMeanAdjacency ^ (m + 1)) 0 1) +
        ((goldenMeanAdjacency ^ m) 0 0 + (goldenMeanAdjacency ^ m) 0 1) from by ring]
    rw [ih1, ih0, ← Nat.cast_add]
    congr 1
    exact (Omega.fib_succ_succ' (m + 2)).symm


/-- Helper: entry (i,j) of A^(m+2) = entry of A^(m+1) + entry of A^m. -/
private theorem pow_entry_add_two (m : Nat) (i j : Fin 2) :
    (goldenMeanAdjacency ^ (m + 2)) i j =
      (goldenMeanAdjacency ^ (m + 1)) i j + (goldenMeanAdjacency ^ m) i j := by
  have := goldenMeanAdjacency_pow_add_two m
  exact congr_fun (congr_fun (congr_arg Matrix.of this) i) j

/-- (A^m)_{00} = F_{m+1}.
    thm:golden-mean-pow-entry-00 -/
theorem goldenMeanAdjacency_pow_00 :
    ∀ m : Nat, (goldenMeanAdjacency ^ m) 0 0 = (Nat.fib (m + 1) : ℤ)
  | 0 => by native_decide
  | 1 => by native_decide
  | m + 2 => by
    rw [pow_entry_add_two, goldenMeanAdjacency_pow_00 (m + 1),
        goldenMeanAdjacency_pow_00 m, ← Nat.cast_add]
    congr 1; exact (Omega.fib_succ_succ' (m + 1)).symm

/-- (A^m)_{01} = F_m.
    thm:golden-mean-pow-entry-01 -/
theorem goldenMeanAdjacency_pow_01 :
    ∀ m : Nat, (goldenMeanAdjacency ^ m) 0 1 = (Nat.fib m : ℤ)
  | 0 => by native_decide
  | 1 => by native_decide
  | m + 2 => by
    rw [pow_entry_add_two, goldenMeanAdjacency_pow_01 (m + 1),
        goldenMeanAdjacency_pow_01 m, ← Nat.cast_add]
    congr 1; exact (Omega.fib_succ_succ' m).symm

/-- (A^m)_{10} = F_m.
    thm:golden-mean-pow-entry-10 -/
theorem goldenMeanAdjacency_pow_10 :
    ∀ m : Nat, (goldenMeanAdjacency ^ m) 1 0 = (Nat.fib m : ℤ)
  | 0 => by native_decide
  | 1 => by native_decide
  | m + 2 => by
    rw [pow_entry_add_two, goldenMeanAdjacency_pow_10 (m + 1),
        goldenMeanAdjacency_pow_10 m, ← Nat.cast_add]
    congr 1; exact (Omega.fib_succ_succ' m).symm

/-- (A^m)_{11} = F_{m-1} for m ≥ 1.
    thm:golden-mean-pow-entry-11 -/
theorem goldenMeanAdjacency_pow_11 :
    ∀ m : Nat, (goldenMeanAdjacency ^ (m + 1)) 1 1 = (Nat.fib m : ℤ)
  | 0 => by native_decide
  | 1 => by native_decide
  | m + 2 => by
    rw [show m + 2 + 1 = (m + 1 + 1) + 1 from by omega,
        show (m + 1 + 1) + 1 = (m + 1) + 2 from by omega,
        pow_entry_add_two,
        goldenMeanAdjacency_pow_11 (m + 1), goldenMeanAdjacency_pow_11 m, ← Nat.cast_add]
    congr 1; exact (Omega.fib_succ_succ' m).symm

/-- det(A^m) = (-1)^m.
    thm:transfer-matrix-pow-det -/
theorem goldenMeanAdjacency_pow_det (m : Nat) :
    (goldenMeanAdjacency ^ m).det = (-1 : ℤ) ^ m := by
  rw [Matrix.det_pow]; simp [goldenMeanAdjacency_det]

/-- det(A^n) = (-1)^n for the golden-mean adjacency matrix (alias).
    thm:zeta-syntax-det-pow -/
theorem goldenMean_det_pow_general (n : ℕ) :
    (goldenMeanAdjacency ^ n).det = (-1 : ℤ) ^ n :=
  goldenMeanAdjacency_pow_det n

/-- A^m as a Fibonacci matrix: all four entries in one statement.
    thm:golden-mean-pow-fibonacci-matrix -/
theorem goldenMeanAdjacency_pow_eq_fib_matrix (m : Nat) (hm : 1 ≤ m) :
    (goldenMeanAdjacency ^ m) 0 0 = (Nat.fib (m + 1) : ℤ) ∧
    (goldenMeanAdjacency ^ m) 0 1 = (Nat.fib m : ℤ) ∧
    (goldenMeanAdjacency ^ m) 1 0 = (Nat.fib m : ℤ) ∧
    (goldenMeanAdjacency ^ m) 1 1 = (Nat.fib (m - 1) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ⟨goldenMeanAdjacency_pow_00 (1 + k),
    goldenMeanAdjacency_pow_01 (1 + k),
    goldenMeanAdjacency_pow_10 (1 + k),
    ?_⟩
  rw [show 1 + k = k + 1 from by omega]
  simp only [show k + 1 - 1 = k from by omega]
  exact goldenMeanAdjacency_pow_11 k

/-- Cassini's identity: F_{n+1}·F_{n-1} - F_n² = (-1)^n for n ≥ 1.
    thm:fib-cassini-identity -/
theorem fib_cassini (n : Nat) (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℤ) * Nat.fib (n - 1) - (Nat.fib n : ℤ) ^ 2 = (-1 : ℤ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- det(A^{m+1}) = (A^{m+1})_{00}·(A^{m+1})_{11} - (A^{m+1})_{01}·(A^{m+1})_{10}
  have hDet := goldenMeanAdjacency_pow_det (m + 1)
  simp only [Matrix.det_fin_two, goldenMeanAdjacency_pow_00,
    goldenMeanAdjacency_pow_01, goldenMeanAdjacency_pow_10,
    goldenMeanAdjacency_pow_11] at hDet
  -- hDet : F_{m+2}·F_m - F_{m+1}·F_{m+1} = (-1)^{m+1}
  simp only [show m + 1 - 1 = m from by omega] at *
  -- hDet : ↑(F_{m+2}) * ↑(F_m) - ↑(F_{m+1}) * ↑(F_{m+1}) = (-1)^(m+1)
  -- Goal: ↑(F_{m+2}) * ↑(F_m) - ↑(F_{m+1})^2 = (-1)^(m+1)
  rw [sq]; exact hDet

/-- Row 1 sum of A^m: paths starting from state 1.
    thm:golden-mean-path-count-from-true -/
theorem goldenMean_path_count_from_true (m : Nat) :
    (goldenMeanAdjacency ^ m) 1 0 + (goldenMeanAdjacency ^ m) 1 1 =
      (Nat.fib (m + 1) : ℤ) := by
  cases m with
  | zero => native_decide
  | succ m =>
    rw [goldenMeanAdjacency_pow_10, goldenMeanAdjacency_pow_11, ← Nat.cast_add]
    congr 1; exact (Omega.fib_succ_succ' m).symm

/-- Total paths of length m in the golden-mean shift.
    thm:golden-mean-total-paths -/
theorem goldenMean_total_paths (m : Nat) :
    (goldenMeanAdjacency ^ m) 0 0 + (goldenMeanAdjacency ^ m) 0 1 +
    ((goldenMeanAdjacency ^ m) 1 0 + (goldenMeanAdjacency ^ m) 1 1) =
      (Nat.fib (m + 2) + Nat.fib (m + 1) : ℤ) := by
  rw [goldenMeanAdjacency_row_sum, goldenMean_path_count_from_true, ← Nat.cast_add]

/-- Specific power entries: (A^5)_{00} = F(6) = 8.
    thm:transfer-matrix-pow-five-00 -/
theorem goldenMeanAdjacency_pow_five_00 :
    (goldenMeanAdjacency ^ 5) 0 0 = (Nat.fib 6 : ℤ) :=
  goldenMeanAdjacency_pow_00 5

/-- Specific power entries: (A^6)_{00} = F(7) = 13.
    thm:transfer-matrix-pow-six-00 -/
theorem goldenMeanAdjacency_pow_six_00 :
    (goldenMeanAdjacency ^ 6) 0 0 = (Nat.fib 7 : ℤ) :=
  goldenMeanAdjacency_pow_00 6

/-- Specific power entries: (A^10)_{00} = F(11) = 89.
    thm:transfer-matrix-pow-ten-00 -/
theorem goldenMeanAdjacency_pow_ten_00 :
    (goldenMeanAdjacency ^ 10) 0 0 = (Nat.fib 11 : ℤ) :=
  goldenMeanAdjacency_pow_00 10

/-! ### Golden-mean zeta function -/

/-- Zeta denominator evaluation at z=1: 1 - tr(A) + det(A) = 1 - 1 + (-1) = -1.
    prop:pom-zeta-golden-mean-denom-at-one -/
theorem goldenMean_zeta_denom_at_one :
    (1 : ℤ) - goldenMeanAdjacency.trace + goldenMeanAdjacency.det = -1 := by
  rw [goldenMeanAdjacency_trace, goldenMeanAdjacency_det]; norm_num

/-- Golden-mean trace recurrence verified for n = 0..4.
    prop:pom-trace-recurrence-verified -/
theorem goldenMean_trace_recurrence_verified :
    (goldenMeanAdjacency ^ 2).trace = (goldenMeanAdjacency ^ 1).trace + (goldenMeanAdjacency ^ 0).trace ∧
    (goldenMeanAdjacency ^ 3).trace = (goldenMeanAdjacency ^ 2).trace + (goldenMeanAdjacency ^ 1).trace ∧
    (goldenMeanAdjacency ^ 4).trace = (goldenMeanAdjacency ^ 3).trace + (goldenMeanAdjacency ^ 2).trace ∧
    (goldenMeanAdjacency ^ 5).trace = (goldenMeanAdjacency ^ 4).trace + (goldenMeanAdjacency ^ 3).trace ∧
    (goldenMeanAdjacency ^ 6).trace = (goldenMeanAdjacency ^ 5).trace + (goldenMeanAdjacency ^ 4).trace := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ### Perron--Frobenius data for the golden-mean adjacency matrix -/

open scoped goldenRatio

/-- The golden-mean adjacency matrix over `ℝ`. -/
noncomputable def goldenMeanAdjacencyℝ : Matrix (Fin 2) (Fin 2) ℝ :=
  goldenMeanAdjacency.map fun z : ℤ => (z : ℝ)

/-- The vector `(φ, 1)`. -/
noncomputable def goldenMeanEigenvector : Fin 2 → ℝ
  | 0 => Real.goldenRatio
  | 1 => 1

@[simp] theorem goldenMeanEigenvector_zero : goldenMeanEigenvector 0 = Real.goldenRatio := rfl
@[simp] theorem goldenMeanEigenvector_one : goldenMeanEigenvector 1 = 1 := rfl

/-- The golden-mean adjacency matrix over `ℝ`, written explicitly. -/
theorem goldenMeanAdjacencyℝ_eq :
    goldenMeanAdjacencyℝ = !![(1 : ℝ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [goldenMeanAdjacencyℝ, goldenMeanAdjacency]

/-- The vector `(φ,1)` is a concrete positive eigenvector candidate. -/
theorem goldenMeanAdjacency_mul_goldenEigenvector :
    Matrix.mulVec goldenMeanAdjacencyℝ goldenMeanEigenvector
      = fun i => Real.goldenRatio * goldenMeanEigenvector i := by
  rw [goldenMeanAdjacencyℝ_eq]
  funext i
  fin_cases i
  · simp [goldenMeanEigenvector, Matrix.mulVec, dotProduct]
    nlinarith [Real.goldenRatio_sq]
  · simp [goldenMeanEigenvector, Matrix.mulVec, dotProduct]

/-- Any `φ`-eigenvector satisfies the Perron coordinate ratio `w₀ = φ w₁`.
    thm:golden-mean-pf-root-eq-phi -/
theorem goldenMeanAdjacency_phi_eigenvector_ratio
    {w : Fin 2 → ℝ}
    (hμ : Matrix.mulVec goldenMeanAdjacencyℝ w = fun i => Real.goldenRatio * w i) :
    w 0 = Real.goldenRatio * w 1 := by
  have h1 := congrFun hμ 1
  rw [goldenMeanAdjacencyℝ_eq] at h1
  simpa [Matrix.mulVec, dotProduct] using h1

/-- Concrete witness form of the golden-ratio eigenvalue statement.
    lem:golden-mean-has-phi-eigenvector -/
theorem goldenMeanAdjacency_has_goldenRatio_eigenvector :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧
      Matrix.mulVec goldenMeanAdjacencyℝ v = fun i => Real.goldenRatio * v i := by
  refine ⟨goldenMeanEigenvector, ?_, goldenMeanAdjacency_mul_goldenEigenvector⟩
  intro h
  have h0 := congrFun h 0
  have hphi : Real.goldenRatio = 0 := by simpa [goldenMeanEigenvector] using h0
  exact Real.goldenRatio_ne_zero hphi

/-- The scalar equation `φ² - φ - 1 = 0`.
    aux:golden-mean-charpoly-eval-phi -/
theorem goldenMeanAdjacency_charpoly_eval_goldenRatio :
    Real.goldenRatio ^ 2 - Real.goldenRatio - 1 = 0 := by
  nlinarith [Real.goldenRatio_sq]

/-- The scalar equation `ψ² - ψ - 1 = 0`.
    aux:golden-mean-charpoly-eval-psi -/
theorem goldenMeanAdjacency_charpoly_eval_goldenConj :
    Real.goldenConj ^ 2 - Real.goldenConj - 1 = 0 := by
  nlinarith [Real.goldenConj_sq]

/-- The real golden-mean adjacency matrix satisfies the same quadratic relation.
    aux:golden-mean-adjacency-real-square -/
theorem goldenMeanAdjacencyℝ_sq :
    goldenMeanAdjacencyℝ ^ 2 = goldenMeanAdjacencyℝ + 1 := by
  rw [goldenMeanAdjacencyℝ_eq, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_fin_two]

/-- Any real eigenvalue of the golden-mean adjacency matrix satisfies `μ² = μ + 1`.
    lem:golden-mean-real-eigenvalue-quadratic -/
theorem eigenvalue_satisfies_quadratic
    {μ : ℝ} {w : Fin 2 → ℝ}
    (hw : w ≠ 0)
    (hμ : Matrix.mulVec goldenMeanAdjacencyℝ w = fun i => μ * w i) :
    μ ^ 2 = μ + 1 := by
  have h0 := congrFun hμ 0
  have h1 := congrFun hμ 1
  rw [goldenMeanAdjacencyℝ_eq] at h0 h1
  simp [Matrix.mulVec, dotProduct] at h0 h1
  by_cases hw1 : w 1 = 0
  · have hw0 : w 0 ≠ 0 := by
      intro hw0
      apply hw
      funext i
      fin_cases i <;> simp [hw0, hw1]
    have h00 : w 0 = 0 := by simpa [hw1] using h1
    exact (hw0 h00).elim
  · have hsub : (μ + 1) * w 1 = μ ^ 2 * w 1 := by
      calc
        (μ + 1) * w 1 = μ * w 1 + w 1 := by ring
        _ = w 0 + w 1 := by rw [h1]
        _ = μ * w 0 := by simpa using h0
        _ = μ * (μ * w 1) := by rw [h1]
        _ = μ ^ 2 * w 1 := by ring
    have hquadw1 : (μ ^ 2 - μ - 1) * w 1 = 0 := by
      nlinarith [hsub]
    have hquad : μ ^ 2 - μ - 1 = 0 := by
      have hquadw1' : (μ ^ 2 - μ - 1) * w 1 = 0 * w 1 := by simpa using hquadw1
      exact mul_right_cancel₀ hw1 hquadw1'
    nlinarith [hquad]

/-- Any real eigenvalue is either `φ` or `ψ`.
    lem:golden-mean-real-eigenvalue-classification -/
theorem eigenvalue_eq_goldenRatio_or_goldenConj
    {μ : ℝ} (hμ : μ ^ 2 = μ + 1) :
    μ = Real.goldenRatio ∨ μ = Real.goldenConj := by
  have hfactor : (μ - Real.goldenRatio) * (μ - Real.goldenConj) = 0 := by
    nlinarith [hμ, Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]
  exact mul_eq_zero.mp hfactor |>.elim
    (fun h => Or.inl <| sub_eq_zero.mp h)
    (fun h => Or.inr <| sub_eq_zero.mp h)

/-- The golden conjugate has strictly smaller modulus than `φ`.
    lem:golden-conj-abs-lt-phi -/
theorem goldenConj_abs_lt_goldenRatio :
    |Real.goldenConj| < Real.goldenRatio := by
  have hψ : |Real.goldenConj| < 1 := by
    rw [abs_lt]
    exact ⟨by linarith [Real.neg_one_lt_goldenConj], by linarith [Real.goldenConj_neg]⟩
  exact lt_trans hψ Real.one_lt_goldenRatio

/-- Every real eigenvalue is dominated in modulus by `φ`.
    prop:golden-mean-real-eigenvalues-bounded-by-phi -/
theorem goldenMeanAdjacency_dominates_all_real_eigenvalues
    {μ : ℝ}
    (hμ : ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ Matrix.mulVec goldenMeanAdjacencyℝ w = fun i => μ * w i) :
    |μ| ≤ Real.goldenRatio := by
  rcases hμ with ⟨w, hw, hwμ⟩
  rcases eigenvalue_eq_goldenRatio_or_goldenConj (eigenvalue_satisfies_quadratic hw hwμ) with rfl | rfl
  · rw [abs_of_pos Real.goldenRatio_pos]
  · exact le_of_lt goldenConj_abs_lt_goldenRatio

/-- Concrete Perron-root package for the golden-mean adjacency matrix.
    thm:golden-mean-pf-root-eq-phi -/
theorem goldenMeanAdjacency_pf_root_eq_goldenRatio :
    ∃ v : Fin 2 → ℝ,
      (0 < v 0 ∧ 0 < v 1) ∧
      (Matrix.mulVec goldenMeanAdjacencyℝ v = fun i => Real.goldenRatio * v i) ∧
      (∀ μ : ℝ, (∃ w : Fin 2 → ℝ, w ≠ 0 ∧ Matrix.mulVec goldenMeanAdjacencyℝ w = fun i => μ * w i) →
        |μ| ≤ Real.goldenRatio) := by
  refine ⟨goldenMeanEigenvector, ?_, goldenMeanAdjacency_mul_goldenEigenvector, ?_⟩
  · exact ⟨Real.goldenRatio_pos, by norm_num⟩
  · intro μ hμ
    exact goldenMeanAdjacency_dominates_all_real_eigenvalues hμ

/-- A positive real eigenvector forces the Perron root `φ`.
    thm:golden-mean-pf-root-eq-phi -/
theorem goldenMeanAdjacency_positive_eigenvalue_eq_goldenRatio
    {μ : ℝ} {w : Fin 2 → ℝ}
    (hw : w ≠ 0)
    (hpos : 0 < w 0 ∧ 0 < w 1)
    (hμ : Matrix.mulVec goldenMeanAdjacencyℝ w = fun i => μ * w i) :
    μ = Real.goldenRatio := by
  rcases eigenvalue_eq_goldenRatio_or_goldenConj (eigenvalue_satisfies_quadratic hw hμ) with hφ | hψ
  · exact hφ
  · have h1 := congrFun hμ 1
    rw [goldenMeanAdjacencyℝ_eq] at h1
    simp [Matrix.mulVec, dotProduct] at h1
    have hμpos : 0 < μ := by
      rw [hψ] at h1
      nlinarith [hpos.1, hpos.2, Real.goldenConj_neg]
    rw [hψ] at hμpos
    linarith [Real.goldenConj_neg]

/-- Any strictly positive `φ`-eigenvector is a positive scalar multiple of `(φ,1)`.
    thm:golden-mean-positive-eigenvector-rigidity -/
theorem goldenMeanAdjacency_positive_eigenvector_rigidity
    {w : Fin 2 → ℝ}
    (hw : w ≠ 0)
    (hpos : 0 < w 0 ∧ 0 < w 1)
    (hμ : Matrix.mulVec goldenMeanAdjacencyℝ w = fun i => Real.goldenRatio * w i) :
    ∃ c : ℝ, 0 < c ∧ w = fun i => c * goldenMeanEigenvector i := by
  have h1 := congrFun hμ 1
  rw [goldenMeanAdjacencyℝ_eq] at h1
  simp [Matrix.mulVec, dotProduct] at h1
  have hw1_ne : w 1 ≠ 0 := by
    intro hw1_zero
    have hw0_zero : w 0 = 0 := by simpa [hw1_zero] using h1
    apply hw
    funext i
    fin_cases i <;> simp [hw0_zero, hw1_zero]
  refine ⟨w 1, hpos.2, ?_⟩
  funext i
  fin_cases i
  · simpa [goldenMeanEigenvector, mul_comm] using h1
  · simp [goldenMeanEigenvector]

-- ══════════════════════════════════════════════════════════════
-- Phase 185
-- ══════════════════════════════════════════════════════════════

/-- The golden mean adjacency matrix satisfies A² = A + I (Cayley-Hamilton). -/
theorem goldenMeanAdjacency_cayley_hamilton :
    goldenMeanAdjacency ^ 2 = goldenMeanAdjacency + 1 :=
  goldenMeanAdjacency_sq

-- ══════════════════════════════════════════════════════════════
-- Phase 209: Row sum + fusion rule (named wrappers)
-- ══════════════════════════════════════════════════════════════

/-- Row 0 sum of A^m = F(m+2). Counts all length-m paths from state 0.
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem goldenMeanAdjacency_pow_row0_sum (m : Nat) (_hm : 1 ≤ m) :
    (goldenMeanAdjacency ^ m) 0 0 + (goldenMeanAdjacency ^ m) 0 1 = (Nat.fib (m + 2) : ℤ) :=
  goldenMeanAdjacency_row_sum m

/-- Fibonacci fusion rule: A^2 = A + I. Matrix realization of tau^2 = 1 + tau.
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem goldenMeanAdjacency_fusion_rule :
    goldenMeanAdjacency ^ 2 = goldenMeanAdjacency + 1 :=
  goldenMeanAdjacency_sq

-- ══════════════════════════════════════════════════════════════
-- Phase 222: Transfer matrix symmetry
-- ══════════════════════════════════════════════════════════════

/-- Transfer matrix is symmetric: A^T = A.
    prop:Phi_m-entropy -/
theorem goldenMeanAdjacency_symmetric :
    goldenMeanAdjacency.transpose = goldenMeanAdjacency := by native_decide

/-- A^m is symmetric for all m.
    prop:Phi_m-entropy -/
theorem goldenMeanAdjacency_pow_symmetric (m : Nat) :
    (goldenMeanAdjacency ^ m).transpose = goldenMeanAdjacency ^ m := by
  rw [Matrix.transpose_pow, goldenMeanAdjacency_symmetric]

/-- The adjacency matrix A + A² has all positive entries (irreducibility/primitivity).
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem goldenMeanAdjacency_irreducible :
    ∀ i j : Fin 2, 0 < (goldenMeanAdjacency + goldenMeanAdjacency ^ 2) i j := by
  native_decide

/-- All entries of A^n are nonneg (they are Fibonacci numbers).
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem goldenMeanAdjacency_pow_nonneg (n : Nat) (i j : Fin 2) :
    0 ≤ (goldenMeanAdjacency ^ n) i j := by
  -- All entries are Nat.fib values cast to ℤ, hence ≥ 0
  have h00 : (goldenMeanAdjacency ^ n) 0 0 = (Nat.fib (n + 1) : ℤ) := goldenMeanAdjacency_pow_00 n
  have h01 : (goldenMeanAdjacency ^ n) 0 1 = (Nat.fib n : ℤ) := goldenMeanAdjacency_pow_01 n
  have h10 : (goldenMeanAdjacency ^ n) 1 0 = (Nat.fib n : ℤ) := goldenMeanAdjacency_pow_10 n
  have h11 : ∀ m, (goldenMeanAdjacency ^ (m + 1)) 1 1 = (Nat.fib m : ℤ) := goldenMeanAdjacency_pow_11
  fin_cases i <;> fin_cases j <;> simp only [show (0 : Fin 2) = ⟨0, by omega⟩ from rfl,
    show (1 : Fin 2) = ⟨1, by omega⟩ from rfl] at *
  · linarith
  · linarith
  · linarith
  · cases n with
    | zero => native_decide
    | succ m => linarith [h11 m]

/-- All entries of A^n are strictly positive for n ≥ 2 (primitive matrix).
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem goldenMeanAdjacency_pow_positive (n : Nat) (hn : 2 ≤ n) (i j : Fin 2) :
    0 < (goldenMeanAdjacency ^ n) i j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h00 := goldenMeanAdjacency_pow_00 (m + 2)
  have h01 := goldenMeanAdjacency_pow_01 (m + 2)
  have h10 := goldenMeanAdjacency_pow_10 (m + 2)
  have h11 := goldenMeanAdjacency_pow_11 (m + 1)
  rw [show m + 1 + 1 = m + 2 from by omega] at h11
  fin_cases i <;> fin_cases j <;> simp only [show (0 : Fin 2) = ⟨0, by omega⟩ from rfl,
    show (1 : Fin 2) = ⟨1, by omega⟩ from rfl] at *
  · linarith [Nat.fib_pos.mpr (show 0 < m + 3 from by omega)]
  · linarith [Nat.fib_pos.mpr (show 0 < m + 2 from by omega)]
  · linarith [Nat.fib_pos.mpr (show 0 < m + 2 from by omega)]
  · linarith [Nat.fib_pos.mpr (show 0 < m + 1 from by omega)]

end Omega.Graph
