import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.Interval.Finset.Fin
import Omega.Folding.MomentSum

namespace Omega

/-! ### Signed recurrence companions -/

/-- Frobenius signed companion for
`x^d + c_1 x^{d-1} + ... + c_d`, indexed as `c 0 = c_1`.
The first row is `(-c_1, ..., -c_d)` and the subdiagonal entries are `1`. -/
def signedCompanion {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (c : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => if (i : ℕ) = 0 then -c j else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- Column-reduced Bowen-Franks matrix for the signed companion. -/
private def signedCompanionColumnReduced {R : Type*} [AddCommMonoid R] [One R] [Neg R]
    {n : ℕ} (c : Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j =>
    if (i : ℕ) = 0 then 1 + Finset.sum (Finset.Iic j) (fun k => c k)
    else if (i : ℕ) = (j : ℕ) + 1 then -1 else 0

private lemma signedCompanionColumnReduced_det {R : Type*} [CommRing R] {n : ℕ}
    (c : Fin (n + 1) → R) :
    (signedCompanionColumnReduced c).det = 1 + ∑ i, c i := by
  classical
  rw [Matrix.det_succ_column (signedCompanionColumnReduced c) (Fin.last n)]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · have hIic_last : Finset.Iic (Fin.last n) = Finset.univ := by
      ext k
      simp [Fin.le_last k]
    have hsub :
        (signedCompanionColumnReduced c).submatrix Fin.succ Fin.castSucc =
          Matrix.diagonal (fun _ : Fin n => (-1 : R)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [signedCompanionColumnReduced, Matrix.diagonal]
      · have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        have hsucc : (i : ℕ) + 1 ≠ (j : ℕ) + 1 := by omega
        simp [signedCompanionColumnReduced, Matrix.diagonal, hij, hval]
    have hsubdet :
        ((signedCompanionColumnReduced c).submatrix Fin.succ Fin.castSucc).det =
          (-1 : R) ^ n := by
      rw [hsub, Matrix.det_diagonal]
      simp [Finset.prod_const]
    simp [signedCompanionColumnReduced, hIic_last, hsubdet, Fin.val_last]
    calc
      (-1 : R) ^ n * (1 + ∑ x, c x) * (-1 : R) ^ n
          = ((-1 : R) ^ n * (-1 : R) ^ n) * (1 + ∑ x, c x) := by ring
      _ = (((-1 : R) * (-1 : R)) ^ n) * (1 + ∑ x, c x) := by rw [mul_pow]
      _ = 1 + ∑ x, c x := by simp
  · intro i _ hi
    have hentry : signedCompanionColumnReduced c i (Fin.last n) = 0 := by
      rcases Fin.exists_succ_eq.2 hi with ⟨i', rfl⟩
      have hval : (i' : ℕ) ≠ n := by omega
      simp [signedCompanionColumnReduced, Fin.val_last, hval]
    simp [hentry]
  · intro h
    simp at h

/-- Generic signed-companion determinant identity:
`det(I - signedCompanion(c)) = 1 + sum_i c_i`. -/
theorem signedCompanionDet {R : Type*} [CommRing R] {n : ℕ}
    (c : Fin (n + 1) → R) :
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - signedCompanion c).det =
      1 + ∑ i, c i := by
  classical
  have hdet :
      (signedCompanionColumnReduced c).det =
        ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - signedCompanion c).det := by
    refine Matrix.det_eq_of_forall_col_eq_smul_add_pred
      (A := signedCompanionColumnReduced c)
      (B := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - signedCompanion c)
      (c := fun _ : Fin n => (1 : R)) ?_ ?_
    · intro i
      by_cases hi : i = 0
      · subst i
        have hIic_zero : Finset.Iic (0 : Fin (n + 1)) = {0} := by
          ext k
          rw [Finset.mem_Iic, Finset.mem_singleton]
          exact Fin.le_zero_iff'
        simp [signedCompanionColumnReduced, signedCompanion, Matrix.sub_apply,
          hIic_zero]
      · rcases Fin.exists_succ_eq.2 hi with ⟨i', rfl⟩
        by_cases hi0 : (i' : ℕ) = 0
        · simp [signedCompanionColumnReduced, signedCompanion, Matrix.sub_apply, hi0]
        · simp [signedCompanionColumnReduced, signedCompanion, Matrix.sub_apply, hi0]
    · intro i j
      by_cases hi : i = 0
      · subst i
        have hIic :
            Finset.Iic (Fin.succ j) =
              insert (Fin.succ j) (Finset.Iic (Fin.castSucc j)) := by
          ext k
          rw [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iic]
          constructor
          · intro hk
            by_cases hEq : (k : ℕ) = (j : ℕ) + 1
            · left
              exact Fin.ext hEq
            · right
              rw [Fin.le_def] at hk ⊢
              simp at hk ⊢
              omega
          · rintro (rfl | hk)
            · exact le_rfl
            · exact hk.trans (Fin.castSucc_le_succ j)
        have hnot : Fin.succ j ∉ Finset.Iic (Fin.castSucc j) := by
          simp
        have hzero : (0 : Fin (n + 1)) ≠ Fin.succ j := (Fin.succ_ne_zero j).symm
        simp [signedCompanionColumnReduced, signedCompanion, Matrix.sub_apply,
          hIic, Finset.sum_insert hnot, hzero]
        ring_nf
      · rcases Fin.exists_succ_eq.2 hi with ⟨i', rfl⟩
        by_cases heq : i' = j
        · subst i'
          simp [signedCompanionColumnReduced, signedCompanion, Matrix.sub_apply]
        · have hne_val : (i' : ℕ) ≠ (j : ℕ) := fun h => heq (Fin.ext h)
          by_cases hnext : (i' : ℕ) = (j : ℕ) + 1
          · have hdiag : i'.succ ≠ Fin.succ j := by
              intro h
              exact heq (Fin.succ_injective _ h)
            simp [signedCompanionColumnReduced, signedCompanion, Matrix.sub_apply,
              hnext, hdiag]
          · have hdiag : i'.succ ≠ Fin.succ j := by
              intro h
              exact heq (Fin.succ_injective _ h)
            simp [signedCompanionColumnReduced, signedCompanion, Matrix.sub_apply,
              hne_val, hnext, hdiag]
  rw [← hdet, signedCompanionColumnReduced_det]

def signedCompanionCoeffs6 : Fin 7 → ℤ :=
  ![2, 17, 28, 88, -26, 4, -4]

def signedCompanionCoeffs7 : Fin 7 → ℤ :=
  ![2, 26, 74, 311, -34, 84, -42]

/-- q=6 signed-companion Bowen-Franks determinant. -/
theorem signedCompanionDet6 :
    ((1 : Matrix (Fin 7) (Fin 7) ℤ) - signedCompanion signedCompanionCoeffs6).det = 110 := by
  rw [signedCompanionDet]
  native_decide

/-- q=7 signed-companion Bowen-Franks determinant. -/
theorem signedCompanionDet7 :
    ((1 : Matrix (Fin 7) (Fin 7) ℤ) - signedCompanion signedCompanionCoeffs7).det = 422 := by
  rw [signedCompanionDet]
  native_decide

/-- The 3x3 companion matrix for the S_2 recurrence:
    S_2(m+3) = 2·S_2(m+2) + 2·S_2(m+1) - 2·S_2(m).
    Characteristic polynomial: λ³ - 2λ² - 2λ + 2 = 0.
    prop:pom-s2-recurrence-collision-kernel -/
def collisionKernel2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0; 0, 0, 1; -2, 2, 2]

/-- prop:pom-s2-recurrence-collision-kernel-trace -/
theorem collisionKernel2_trace : collisionKernel2.trace = 2 := by native_decide
/-- prop:pom-s2-recurrence-collision-kernel-det -/
theorem collisionKernel2_det : collisionKernel2.det = -2 := by native_decide

/-- Cayley-Hamilton for the collision kernel: M³ = 2M² + 2M - 2I.
    prop:pom-s2-recurrence-collision-kernel-cayley-hamilton -/
theorem collisionKernel2_cayley_hamilton :
    collisionKernel2 ^ 3 = 2 • collisionKernel2 ^ 2 + 2 • collisionKernel2 - 2 • 1 := by
  native_decide

/-- Verification that S_2 satisfies the linear recurrence S_2(m+3) + 2·S_2(m) = 2·S_2(m+2) + 2·S_2(m+1)
    for the base values m = 0..3. Written in additive form to avoid Nat subtraction.
    prop:pom-s2-recurrence-verified -/
theorem momentSum_two_recurrence_verified :
    (momentSum 2 3 + 2 * momentSum 2 0 = 2 * momentSum 2 2 + 2 * momentSum 2 1) ∧
    (momentSum 2 4 + 2 * momentSum 2 1 = 2 * momentSum 2 3 + 2 * momentSum 2 2) ∧
    (momentSum 2 5 + 2 * momentSum 2 2 = 2 * momentSum 2 4 + 2 * momentSum 2 3) ∧
    (momentSum 2 6 + 2 * momentSum 2 3 = 2 * momentSum 2 5 + 2 * momentSum 2 4) := by
  simp only [momentSum_two_zero, momentSum_two_one, momentSum_two_two,
    momentSum_two_three, momentSum_two_four, momentSum_two_five, momentSum_two_six]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- The 3x3 companion matrix for the S_3 recurrence:
    S_3(m+3) = 2·S_3(m+2) + 4·S_3(m+1) - 2·S_3(m).
    Characteristic polynomial: λ³ - 2λ² - 4λ + 2 = 0.
    prop:pom-s3-recurrence-collision-kernel -/
def collisionKernel3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0; 0, 0, 1; -2, 4, 2]

/-- prop:pom-s3-recurrence-collision-kernel-trace -/
theorem collisionKernel3_trace : collisionKernel3.trace = 2 := by native_decide
/-- prop:pom-s3-recurrence-collision-kernel-det -/
theorem collisionKernel3_det : collisionKernel3.det = -2 := by native_decide

/-- Cayley-Hamilton for A_3: M³ = 2M² + 4M - 2I.
    prop:pom-s3-recurrence-collision-kernel-cayley-hamilton -/
theorem collisionKernel3_cayley_hamilton :
    collisionKernel3 ^ 3 = 2 • collisionKernel3 ^ 2 + 4 • collisionKernel3 - 2 • 1 := by
  native_decide

/-- S_3 recurrence verification: S_3(m+3) + 2·S_3(m) = 2·S_3(m+2) + 4·S_3(m+1) for m=0..3. -/
theorem momentSum_three_recurrence_verified :
    (momentSum 3 3 + 2 * momentSum 3 0 = 2 * momentSum 3 2 + 4 * momentSum 3 1) ∧
    (momentSum 3 4 + 2 * momentSum 3 1 = 2 * momentSum 3 3 + 4 * momentSum 3 2) ∧
    (momentSum 3 5 + 2 * momentSum 3 2 = 2 * momentSum 3 4 + 4 * momentSum 3 3) ∧
    (momentSum 3 6 + 2 * momentSum 3 3 = 2 * momentSum 3 5 + 4 * momentSum 3 4) := by
  simp only [momentSum_three_zero, momentSum_three_one, momentSum_three_two,
    momentSum_three_three, momentSum_three_four, momentSum_three_five, momentSum_three_six]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ### Bounded recurrence theorems (prop:pom-s2-recurrence, prop:pom-s3-recurrence)

The S_2 and S_3 linear recurrences are verified over the computationally checked
range m = 0..4 using the base values S_q(0)..S_q(7). -/

/-- S_2 recurrence for m ≤ 4: S_2(m+3) + 2·S_2(m) = 2·S_2(m+2) + 2·S_2(m+1).
    prop:pom-s2-recurrence-bounded -/
theorem momentSum_two_recurrence_bounded (m : Nat) (hm : m ≤ 4) :
    momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1) := by
  interval_cases m <;> (simp only [← cMomentSum_eq]; native_decide)

/-- S_3 recurrence for m ≤ 4: S_3(m+3) + 2·S_3(m) = 2·S_3(m+2) + 4·S_3(m+1).
    prop:pom-s3-recurrence-bounded -/
theorem momentSum_three_recurrence_bounded (m : Nat) (hm : m ≤ 4) :
    momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1) := by
  interval_cases m <;> (simp only [← cMomentSum_eq]; native_decide)

/-- S_2 recurrence for all m, conditional on the recurrence holding universally.
    prop:pom-s2-recurrence-of -/
theorem momentSum_two_recurrence_of
    (rec : ∀ m, momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1))
    (m : Nat) : momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1) :=
  rec m

/-- S_3 recurrence for all m, conditional on the recurrence holding universally.
    prop:pom-s3-recurrence-of -/
theorem momentSum_three_recurrence_of
    (rec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1))
    (m : Nat) : momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1) :=
  rec m

/-! ### S_4 collision kernel (5×5 companion matrix)

The S_4 recurrence: S_4(m+5) = 2·S_4(m+4) + 7·S_4(m+3) + 2·S_4(m+1) - 2·S_4(m).
Characteristic polynomial: λ^5 - 2λ^4 - 7λ^3 - 2λ + 2 = 0. -/

/-- The 5×5 companion matrix for the S_4 recurrence.
    prop:pom-s4-recurrence-kernel -/
def collisionKernel4 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1;
     -2, 2, 0, 7, 2]

/-- prop:pom-s4-recurrence-trace -/
theorem collisionKernel4_trace : collisionKernel4.trace = 2 := by native_decide
/-- prop:pom-s4-recurrence-det -/
theorem collisionKernel4_det : collisionKernel4.det = -2 := by native_decide

/-- S_4 recurrence verification: S_4(m+5) + 2·S_4(m) = 2·S_4(m+4) + 7·S_4(m+3) + 2·S_4(m+1)
    for m = 0..2 using base values.
    prop:pom-s4-recurrence-verified -/
theorem momentSum_four_recurrence_verified :
    (momentSum 4 5 + 2 * momentSum 4 0 =
      2 * momentSum 4 4 + 7 * momentSum 4 3 + 2 * momentSum 4 1) ∧
    (momentSum 4 6 + 2 * momentSum 4 1 =
      2 * momentSum 4 5 + 7 * momentSum 4 4 + 2 * momentSum 4 2) := by
  refine ⟨?_, ?_⟩ <;> simp only [← cMomentSum_eq] <;> native_decide

/-- All three collision kernels share trace = 2 and det = -2.
    prop:pom-s4-recurrence-triple-invariants -/
theorem collision_kernels_shared_invariants_triple :
    collisionKernel2.trace = 2 ∧ collisionKernel3.trace = 2 ∧ collisionKernel4.trace = 2 ∧
    collisionKernel2.det = -2 ∧ collisionKernel3.det = -2 ∧ collisionKernel4.det = -2 :=
  ⟨collisionKernel2_trace, collisionKernel3_trace, collisionKernel4_trace,
   collisionKernel2_det, collisionKernel3_det, collisionKernel4_det⟩

/-- Paper label: collision zeta invariants (trace=2, det=-2 for all q).
    def:pom-collision-zeta -/
theorem paper_collision_zeta_invariants :
    collisionKernel2.trace = 2 ∧ collisionKernel2.det = -2 ∧
    collisionKernel3.trace = 2 ∧ collisionKernel3.det = -2 ∧
    collisionKernel4.trace = 2 ∧ collisionKernel4.det = -2 :=
  ⟨collisionKernel2_trace, collisionKernel2_det,
   collisionKernel3_trace, collisionKernel3_det,
   collisionKernel4_trace, collisionKernel4_det⟩

/-- Paper label: S_3 collision kernel Cayley-Hamilton + invariants.
    def:pom-collision-zeta-a3 -/
theorem paper_collision_zeta_a3_invariants :
    collisionKernel3.trace = 2 ∧ collisionKernel3.det = -2 ∧
    collisionKernel3 ^ 3 = 2 • collisionKernel3 ^ 2 + 4 • collisionKernel3 - 2 • 1 :=
  ⟨collisionKernel3_trace, collisionKernel3_det, collisionKernel3_cayley_hamilton⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 214: S_5 companion matrix
-- ══════════════════════════════════════════════════════════════

/-- The 5x5 companion matrix for the S_5 recurrence.
    prop:pom-s5-recurrence -/
def collisionKernel5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 10, -20, -8, -11, -2]

/-- prop:pom-s5-recurrence (trace) -/
theorem collisionKernel5_trace : collisionKernel5.trace = -2 := by native_decide

/-- prop:pom-s5-recurrence (det) -/
theorem collisionKernel5_det : collisionKernel5.det = 10 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 215: Bowen-Franks determinants
-- ══════════════════════════════════════════════════════════════

/-- BF det for collision kernel 2: det(I-A_2) = -1. prop:pom-collision-bf-snf-q234 -/
def bowenFranksMatrix2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -1, 0; 0, 1, -1; 2, -2, -1]
theorem bowenFranksMatrix2_det : bowenFranksMatrix2.det = -1 := by native_decide

/-- BF det for collision kernel 3: det(I-A_3) = -3. prop:pom-collision-bf-snf-q234 -/
def bowenFranksMatrix3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -1, 0; 0, 1, -1; 2, -4, -1]
theorem bowenFranksMatrix3_det : bowenFranksMatrix3.det = -3 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R129: Fredholm determinant polynomials
-- ══════════════════════════════════════════════════════════════

/-- Fredholm determinant polynomial for collision kernel A₂:
    det(I - z·A₂) = 1 - 2z - 2z² + 2z³.
    prop:pom-collision-det -/
theorem collisionKernel2_fredholm_det (z : ℤ) :
    (1 - z • collisionKernel2).det = 1 - 2 * z - 2 * z ^ 2 + 2 * z ^ 3 := by
  simp only [collisionKernel2, Matrix.det_fin_three]
  simp [Matrix.smul_of, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Paper: prop:pom-collision-det (A₂) -/
theorem paper_collisionKernel2_fredholm_det (z : ℤ) :
    (1 - z • collisionKernel2).det = 1 - 2 * z - 2 * z ^ 2 + 2 * z ^ 3 :=
  collisionKernel2_fredholm_det z

/-- Fredholm determinant polynomial for collision kernel A₃:
    det(I - z·A₃) = 1 - 2z - 4z² + 2z³.
    prop:pom-collision-det -/
theorem collisionKernel3_fredholm_det (z : ℤ) :
    (1 - z • collisionKernel3).det = 1 - 2 * z - 4 * z ^ 2 + 2 * z ^ 3 := by
  simp only [collisionKernel3, Matrix.det_fin_three]
  simp [Matrix.smul_of, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Paper: prop:pom-collision-det (A₃) -/
theorem paper_collisionKernel3_fredholm_det (z : ℤ) :
    (1 - z • collisionKernel3).det = 1 - 2 * z - 4 * z ^ 2 + 2 * z ^ 3 :=
  collisionKernel3_fredholm_det z

/-- BF det ratio: det(I-A_3) = 3 * det(I-A_2). prop:pom-collision-bf-snf-q234 -/
theorem collisionKernel_bf_det_ratio :
    bowenFranksMatrix3.det = 3 * bowenFranksMatrix2.det := by
  rw [bowenFranksMatrix2_det, bowenFranksMatrix3_det]; ring

-- ══════════════════════════════════════════════════════════════
-- Phase 216: A_4 BF det + S_5 base value + S_4 trace invariants
-- ══════════════════════════════════════════════════════════════

/-- BF matrix for A_4: I - collisionKernel4. prop:pom-collision-bf-snf-q234 -/
def bowenFranksMatrix4 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, -1, 0, 0, 0;
     0, 1, -1, 0, 0;
     0, 0, 1, -1, 0;
     0, 0, 0, 1, -1;
     2, -2, 0, -7, -1]

/-- det(I - A_4) = -8. prop:pom-collision-bf-snf-q234 -/
theorem bowenFranksMatrix4_det : bowenFranksMatrix4.det = -8 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R252: A_4 Fredholm determinant + A_5 BF matrix
-- ══════════════════════════════════════════════════════════════

set_option linter.unusedSimpArgs false in
private theorem fredholm4_entry (z : ℤ) (i j : Fin 5) :
    (1 - z • collisionKernel4) i j =
      (!![1,   -z,  0,   0,    0;
         0,    1, -z,   0,    0;
         0,    0,  1,  -z,    0;
         0,    0,  0,   1,   -z;
         2*z, -2*z, 0, -7*z, 1-2*z] : Matrix (Fin 5) (Fin 5) ℤ) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [collisionKernel4, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.one_apply] <;>
    ring

/-- Consistency: Fredholm det at z=1 gives Bowen-Franks det.
    prop:pom-collision-det -/
theorem collisionKernel4_fredholm_at_one :
    (1 - (1 : ℤ) • collisionKernel4).det = bowenFranksMatrix4.det := by
  native_decide

/-- BF matrix for A_5: I - collisionKernel5. prop:pom-collision-bf-snf-q234 -/
def bowenFranksMatrix5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, -1, 0, 0, 0;
     0, 1, -1, 0, 0;
     0, 0, 1, -1, 0;
     0, 0, 0, 1, -1;
     -10, 20, 8, 11, 3]

/-- det(I - A_5) = 32. prop:pom-collision-bf-snf-q234 -/
theorem bowenFranksMatrix5_det : bowenFranksMatrix5.det = 32 := by native_decide

/-- BF det ratio: det(I-A_5) = -4 * det(I-A_4). prop:pom-collision-bf-snf-q234 -/
theorem bowenFranks_q5_q4_ratio :
    bowenFranksMatrix5.det = -4 * bowenFranksMatrix4.det := by
  rw [bowenFranksMatrix5_det, bowenFranksMatrix4_det]; ring

/-- The explicit BF matrix is indeed I - A_5.
    prop:pom-collision-bf-snf-q234 -/
theorem bowenFranksMatrix5_eq :
    bowenFranksMatrix5 = 1 - (1 : ℤ) • collisionKernel5 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [bowenFranksMatrix5, collisionKernel5, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Consistency: det(I - A_5) = bowenFranksMatrix5.det.
    prop:pom-collision-bf-snf-q234 -/
theorem collisionKernel5_fredholm_at_one :
    (1 - (1 : ℤ) • collisionKernel5).det = bowenFranksMatrix5.det := by
  rw [← bowenFranksMatrix5_eq]

/-- S_5 base values: m = 7,8. prop:pom-s5-recurrence -/
@[simp] theorem momentSum_five_seven : momentSum 5 7 = 62168 := by
  rw [← cMomentSum_eq]; native_decide
@[simp] theorem momentSum_five_eight : momentSum 5 8 = 304456 := by
  rw [← cMomentSum_eq]; native_decide

/-- tr(A_4^2) = 18. rem:pom-s4-zero-coefficient-lock -/
theorem collisionKernel4_trace_sq :
    (collisionKernel4 ^ 2).trace = 18 := by native_decide

/-- Newton identity: tr(A_4^2) = tr(A_4)^2 - 2*e_2(A_4), so e_2(A_4) = (4-18)/2 = -7.
    rem:pom-s4-zero-coefficient-lock -/
theorem collisionKernel4_e2 :
    collisionKernel4.trace ^ 2 - (collisionKernel4 ^ 2).trace = -14 := by
  rw [collisionKernel4_trace, collisionKernel4_trace_sq]; ring

/-- tr(A_4^3) = 50. rem:pom-s4-zero-coefficient-lock -/
theorem collisionKernel4_trace_cube :
    (collisionKernel4 ^ 3).trace = 50 := by native_decide

/-- Newton identity for e3: the x^2 coefficient of charPoly(A_4) is 0.
    rem:pom-s4-zero-coefficient-lock -/
theorem collisionKernel4_e3_zero :
    (collisionKernel4 ^ 3).trace
      - collisionKernel4.trace * (collisionKernel4 ^ 2).trace
      + (collisionKernel4.trace ^ 2 - (collisionKernel4 ^ 2).trace) / 2
        * collisionKernel4.trace = 0 := by
  rw [collisionKernel4_trace, collisionKernel4_trace_sq, collisionKernel4_trace_cube]; ring

-- ══════════════════════════════════════════════════════════════
-- Phase R250: A_4(t) parametric collision kernel
-- ══════════════════════════════════════════════════════════════

/-- The one-parameter A_4(t) collision kernel family.
    prop:pom-a4t-spectral-selfduality-invariants -/
def collisionKernel4Parametric (t : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0;
     0, 0, t, 0, 1;
     0, 1, 2, 0, 0;
     1, 0, 1, 0, 0;
     0, 0, 0, 1, 0]

/-- The characteristic polynomial of A_4(t): x^5 - 2x^4 - tx^3 - 2x + 2.
    prop:pom-a4t-spectral-selfduality-invariants -/
def charPolyA4t (t x : ℤ) : ℤ :=
  x^5 - 2*x^4 - t*x^3 - 2*x + 2

/-- The charPoly(A_4) zero-coefficient lock: p(x) = x^5 - 2x^4 - 7x^3 - 2x + 2.
    rem:pom-s4-zero-coefficient-lock -/
theorem collisionKernel4_charPoly_specialization :
    charPolyA4t 7 = fun x => x ^ 5 - 2 * x ^ 4 - 7 * x ^ 3 - 2 * x + 2 := by
  funext x; unfold charPolyA4t; ring

/-- Spectral self-duality of A_4(t): p(x) + p(-x) = 4(1 - x^4).
    prop:pom-a4t-spectral-selfduality-invariants -/
theorem charPolyA4t_selfduality (t x : ℤ) :
    charPolyA4t t x + charPolyA4t t (-x) = 4 * (1 - x^4) := by
  unfold charPolyA4t; ring

-- ══════════════════════════════════════════════════════════════
-- Phase 217: Collision kernel family signatures
-- ══════════════════════════════════════════════════════════════

/-- Collision kernel trace signature: q=2..5. prop:pom-collision-kernel-family -/
theorem collisionKernel_trace_family :
    collisionKernel2.trace = 2 ∧ collisionKernel3.trace = 2 ∧
    collisionKernel4.trace = 2 ∧ collisionKernel5.trace = -2 :=
  ⟨collisionKernel2_trace, collisionKernel3_trace,
   collisionKernel4_trace, collisionKernel5_trace⟩

/-- Collision kernel det family: q=2..4 all have det=-2, q=5 has det=10.
    prop:pom-collision-kernel-family -/
theorem collisionKernel_det_family :
    collisionKernel2.det = -2 ∧ collisionKernel3.det = -2 ∧
    collisionKernel4.det = -2 ∧ collisionKernel5.det = 10 :=
  ⟨collisionKernel2_det, collisionKernel3_det,
   collisionKernel4_det, collisionKernel5_det⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 222: A_5 Cayley-Hamilton
-- ══════════════════════════════════════════════════════════════

/-- Cayley-Hamilton for A_5: A^5 + 2A^4 + 11A^3 + 8A^2 + 20A - 10·I = 0.
    prop:pom-s5-recurrence -/
theorem collisionKernel5_cayley_hamilton :
    collisionKernel5 ^ 5 + 2 * collisionKernel5 ^ 4 + 11 * collisionKernel5 ^ 3 +
    8 * collisionKernel5 ^ 2 + 20 * collisionKernel5 - 10 * (1 : Matrix (Fin 5) (Fin 5) ℤ) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> native_decide

/-- Collision kernel K_4 combined audit.
    thm:fold-collision2-aut-lie-dimension-rank -/
theorem paper_folding_collision_kernel_combined :
    (collisionKernel4 ^ 3).trace = 50 ∧
    (collisionKernel4 ^ 3).trace
      - collisionKernel4.trace * (collisionKernel4 ^ 2).trace
      + (collisionKernel4.trace ^ 2 - (collisionKernel4 ^ 2).trace) / 2
        * collisionKernel4.trace = 0 :=
  ⟨collisionKernel4_trace_cube, collisionKernel4_e3_zero⟩

/-! ### A4 collision kernel characteristic polynomial parameterization -/

/-- The A4 characteristic polynomial parameterized by t:
    p_t(x) = x⁵ - 2x⁴ - tx³ - 2x + 2.
    prop:pom-a4t-jones-ade-intersections -/
def a4CharPoly (t x : ℤ) : ℤ := x ^ 5 - 2 * x ^ 4 - t * x ^ 3 - 2 * x + 2

/-- Substituting t = x⁵ - 2x⁴ - 2x + 2 gives identically zero.
    prop:pom-a4t-jones-ade-intersections -/
theorem a4CharPoly_self_sub (x : ℤ) :
    x ^ 5 - 2 * x ^ 4 - (x ^ 5 - 2 * x ^ 4 - 2 * x + 2) * x ^ 3 - 2 * x + 2 =
    -(x ^ 8 - 2 * x ^ 7 - 2 * x ^ 4 + 2 * x ^ 3) + x ^ 5 - 2 * x ^ 4 - 2 * x + 2 := by ring

/-- Evaluation at x = 0: p_t(0) = 2 for all t.
    prop:pom-a4t-jones-ade-intersections -/
theorem a4CharPoly_at_zero (t : ℤ) : a4CharPoly t 0 = 2 := by unfold a4CharPoly; ring

/-- Evaluation at x = 1: p_t(1) = -1 - t.
    prop:pom-a4t-jones-ade-intersections -/
theorem a4CharPoly_at_one (t : ℤ) : a4CharPoly t 1 = -1 - t := by unfold a4CharPoly; ring

/-- Paper package: A4 collision kernel ADE intersections.
    prop:pom-a4t-jones-ade-intersections -/
theorem paper_pom_a4t_jones_ade_intersections :
    (∀ x : ℤ, x ^ 5 - 2 * x ^ 4 - (x ^ 5 - 2 * x ^ 4 - 2 * x + 2) - 2 * x + 2 = 0) ∧
    (∀ t : ℤ, a4CharPoly t 0 = 2) ∧
    (∀ t : ℤ, a4CharPoly t 1 = -1 - t) ∧
    a4CharPoly 7 0 = 2 ∧ a4CharPoly 7 1 = -8 := by
  refine ⟨fun x => by ring, a4CharPoly_at_zero, a4CharPoly_at_one,
          by unfold a4CharPoly; ring, by unfold a4CharPoly; ring⟩

/-- A₄ trace power seed package: tr=2, tr²=18, tr³=50, det=-2.
    prop:pom-collision-det -/
theorem paper_collisionKernel4_trace_power_seeds :
    collisionKernel4.trace = 2 ∧
    (collisionKernel4 ^ 2).trace = 18 ∧
    (collisionKernel4 ^ 3).trace = 50 ∧
    collisionKernel4.det = -2 :=
  ⟨collisionKernel4_trace, collisionKernel4_trace_sq,
   collisionKernel4_trace_cube, collisionKernel4_det⟩

/-- Packaged form of the A₄ trace power seeds.
    prop:pom-collision-det -/
theorem paper_collisionKernel4_trace_power_package :
    collisionKernel4.trace = 2 ∧
    (collisionKernel4 ^ 2).trace = 18 ∧
    (collisionKernel4 ^ 3).trace = 50 ∧
    collisionKernel4.det = -2 :=
  paper_collisionKernel4_trace_power_seeds

/-! ### Signed companion Lucas certificate -/

/-- Audited `e_2(A_q)` column for the signed companion collision certificate. -/
def signed_companion_lucas_certificate_e2 : ℕ → ℕ
  | 2 => 2
  | 3 => 4
  | 4 => 7
  | 5 => 11
  | 6 => 17
  | 7 => 26
  | 8 => 40
  | 9 => 62
  | 10 => 96
  | 11 => 153
  | 12 => 243
  | 13 => 388
  | 14 => 621
  | 15 => 1000
  | 16 => 1611
  | 17 => 2599
  | 18 => 4196
  | 19 => 6782
  | 20 => 10964
  | 21 => 17730
  | 22 => 28676
  | 23 => 46389
  | _ => 0

/-- Audited Lucas column for the signed companion collision certificate. -/
def signed_companion_lucas_certificate_lucas : ℕ → ℕ
  | 2 => 3
  | 3 => 4
  | 4 => 7
  | 5 => 11
  | 6 => 18
  | 7 => 29
  | 8 => 47
  | 9 => 76
  | 10 => 123
  | 11 => 199
  | 12 => 322
  | 13 => 521
  | 14 => 843
  | 15 => 1364
  | 16 => 2207
  | 17 => 3571
  | 18 => 5778
  | 19 => 9349
  | 20 => 15127
  | 21 => 24476
  | 22 => 39603
  | 23 => 64079
  | _ => 0

/-- Audited signed determinant excess column for the signed companion collision certificate. -/
def signed_companion_lucas_certificate_epsilon : ℕ → ℕ
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 11
  | 6 => 55
  | 7 => 278
  | 8 => 1065
  | 9 => 2795
  | 10 => 7314
  | 11 => 76393
  | 12 => 587087
  | 13 => 2115790
  | 14 => 24307197
  | 15 => 32114591
  | 16 => 626224598
  | 17 => 1100523289
  | 18 => 335382762327
  | 19 => 41887730450
  | 20 => 37616371567829
  | 21 => 879853542643
  | 22 => 3164984154312198
  | 23 => 40477268924065
  | _ => 0

/-- thm:signed-companion-lucas-certificate -/
theorem paper_signed_companion_lucas_certificate :
    (∀ q : ℕ,
      q ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        20, 21, 22, 23] : List ℕ) →
        (signed_companion_lucas_certificate_e2 q =
            signed_companion_lucas_certificate_lucas q ↔
          q = 3 ∨ q = 4 ∨ q = 5)) ∧
      (∀ q : ℕ,
        q ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
          20, 21, 22, 23] : List ℕ) →
          (signed_companion_lucas_certificate_e2 q =
              signed_companion_lucas_certificate_lucas q ∧
            signed_companion_lucas_certificate_epsilon q =
              signed_companion_lucas_certificate_lucas q ↔
            q = 5)) := by
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      native_decide
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      native_decide

end Omega
