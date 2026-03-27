import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Omega.Folding.CollisionKernel

namespace Omega

/-! ### Hankel determinant and minimal recurrence order for S_2

The Hankel matrix H_k for a sequence (a_0, a_1, ...) is the k×k matrix with
H_{i,j} = a_{i+j}. For S_q, the 3×3 Hankel determinant is nonzero (so no order-2
recurrence suffices), while the 4×4 Hankel determinant vanishes (consistent
with the order-3 recurrence). -/

/-- The 2×2 Hankel matrix for S_2: [[S_2(0), S_2(1)], [S_2(1), S_2(2)]] = [[1,2],[2,6]]. -/
def hankelS2_2x2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2; 2, 6]

/-- The 2×2 Hankel determinant for S_2 is 2.
    lem:pom-s2-hankel-det-2x2 -/
theorem hankelS2_2x2_det : hankelS2_2x2.det = 2 := by native_decide

/-- The 3×3 Hankel matrix for S_2:
    [[S_2(0), S_2(1), S_2(2)],
     [S_2(1), S_2(2), S_2(3)],
     [S_2(2), S_2(3), S_2(4)]] = [[1,2,6],[2,6,14],[6,14,36]]. -/
def hankelS2_3x3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 6; 2, 6, 14; 6, 14, 36]

/-- The 3×3 Hankel determinant for S_2 is −4 (nonzero).
    lem:pom-s2-hankel-det-3x3 -/
theorem hankelS2_3x3_det : hankelS2_3x3.det = -4 := by native_decide

/-- The 3×3 Hankel determinant is nonzero, so S_2 does not satisfy any order-2
    linear recurrence with constant coefficients.
    lem:pom-s2-hankel-det-nonzero -/
theorem hankelS2_3x3_det_ne_zero : hankelS2_3x3.det ≠ 0 := by
  rw [hankelS2_3x3_det]; omega

/-- The 4×4 Hankel matrix for S_2:
    [[1,2,6,14],[2,6,14,36],[6,14,36,88],[14,36,88,220]]. -/
def hankelS2_4x4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 2, 6, 14; 2, 6, 14, 36; 6, 14, 36, 88; 14, 36, 88, 220]

/-- The 4×4 Hankel determinant for S_2 is 0, consistent with the order-3 recurrence.
    lem:pom-s2-hankel-det-4x4 -/
theorem hankelS2_4x4_det : hankelS2_4x4.det = 0 := by native_decide

/-- The minimal linear recurrence order for S_2 is exactly 3:
    the 3×3 Hankel det is nonzero (order < 3 insufficient) and
    the 4×4 Hankel det is zero (order 3 suffices).
    lem:pom-s2-minimal-order -/
theorem momentSum_two_minimal_recurrence_order :
    hankelS2_3x3.det ≠ 0 ∧ hankelS2_4x4.det = 0 :=
  ⟨hankelS2_3x3_det_ne_zero, hankelS2_4x4_det⟩

/-! ### Hankel determinant for S_3 -/

/-- The 2×2 Hankel matrix for S_3: [[1,2],[2,10]]. -/
def hankelS3_2x2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2; 2, 10]

/-- The 2×2 Hankel determinant for S_3 is 6. -/
theorem hankelS3_2x2_det : hankelS3_2x2.det = 6 := by native_decide

/-- The 3×3 Hankel matrix for S_3: [[1,2,10],[2,10,26],[10,26,88]]. -/
def hankelS3_3x3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 10; 2, 10, 26; 10, 26, 88]

/-- The 3×3 Hankel determinant for S_3 is −108 (nonzero).
    lem:pom-s3-hankel-det-3x3 -/
theorem hankelS3_3x3_det : hankelS3_3x3.det = -108 := by native_decide

/-- The 4×4 Hankel matrix for S_3:
    [[1,2,10,26],[2,10,26,88],[10,26,88,260],[26,88,260,820]]. -/
def hankelS3_4x4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 2, 10, 26; 2, 10, 26, 88; 10, 26, 88, 260; 26, 88, 260, 820]

/-- The 4×4 Hankel determinant for S_3 is 0.
    lem:pom-s3-hankel-det-4x4 -/
theorem hankelS3_4x4_det : hankelS3_4x4.det = 0 := by native_decide

/-- The minimal linear recurrence order for S_3 is also 3.
    lem:pom-s3-minimal-order -/
theorem momentSum_three_minimal_recurrence_order :
    hankelS3_3x3.det ≠ 0 ∧ hankelS3_4x4.det = 0 :=
  ⟨by rw [hankelS3_3x3_det]; omega, hankelS3_4x4_det⟩

/-! ### Characteristic polynomial of collision kernels

The characteristic polynomial of A_2 is λ³ − 2λ² − 2λ + 2.
The characteristic polynomial of A_3 is λ³ − 2λ² − 4λ + 2. -/

/-- The characteristic polynomial of the S_2 collision kernel:
    p(λ) = λ³ − 2λ² − 2λ + 2. -/
theorem collisionKernel2_charpoly :
    collisionKernel2.charpoly = Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 - 2 * Polynomial.X + Polynomial.C 2 := by
  unfold Matrix.charpoly Matrix.charmatrix
  rw [Matrix.det_fin_three]
  simp only [collisionKernel2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply, Fin.isValue]
  simp (config := { decide := true })
  ring

/-- The characteristic polynomial of the S_3 collision kernel:
    p(λ) = λ³ − 2λ² − 4λ + 2. -/
theorem collisionKernel3_charpoly :
    collisionKernel3.charpoly = Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 - 4 * Polynomial.X + Polynomial.C 2 := by
  unfold Matrix.charpoly Matrix.charmatrix
  rw [Matrix.det_fin_three]
  simp only [collisionKernel3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply, Fin.isValue]
  simp (config := { decide := true })
  ring

/-- Evaluation of the characteristic polynomial of A_2 at A_2:
    A_2³ − 2·A_2² − 2·A_2 + 2·I = 0.
    Equivalently: A_2³ + 2·I = 2·A_2² + 2·A_2.
    thm:pom-s2-charpoly-eval -/
theorem collisionKernel2_charpoly_eval :
    collisionKernel2 ^ 3 + 2 • (1 : Matrix (Fin 3) (Fin 3) ℤ) =
      2 • collisionKernel2 ^ 2 + 2 • collisionKernel2 := by
  native_decide

/-- Evaluation of the characteristic polynomial of A_3 at A_3:
    A_3³ − 2·A_3² − 4·A_3 + 2·I = 0.
    Equivalently: A_3³ + 2·I = 2·A_3² + 4·A_3.
    thm:pom-s3-charpoly-eval -/
theorem collisionKernel3_charpoly_eval :
    collisionKernel3 ^ 3 + 2 • (1 : Matrix (Fin 3) (Fin 3) ℤ) =
      2 • collisionKernel3 ^ 2 + 4 • collisionKernel3 := by
  native_decide

/-- The collision kernels A_2 and A_3 have equal traces. -/
theorem collisionKernel_trace_eq : collisionKernel2.trace = collisionKernel3.trace := by
  rw [collisionKernel2_trace, collisionKernel3_trace]

/-- The collision kernels A_2 and A_3 have equal determinants. -/
theorem collisionKernel_det_eq : collisionKernel2.det = collisionKernel3.det := by
  rw [collisionKernel2_det, collisionKernel3_det]

/-- Both collision kernels share trace = 2 and det = −2.
    thm:pom-collision-kernels-shared-invariants -/
theorem collision_kernels_shared_invariants :
    collisionKernel2.trace = collisionKernel3.trace ∧
    collisionKernel2.det = collisionKernel3.det := by
  exact ⟨collisionKernel_trace_eq, collisionKernel_det_eq⟩

/-! ### S_2 resolution monotonicity

S_2(m) ≤ S_2(m+1) for all verified resolutions, and conditionally for all m
assuming the recurrence holds universally. -/

/-- S_2 is strictly increasing on verified resolutions: S_2(m) < S_2(m+1) for m ≤ 6.
    thm:pom-rank-exact-s2-strict-mono -/
theorem momentSum_two_strict_mono_verified (m : Nat) (hm : m ≤ 6) :
    momentSum 2 m < momentSum 2 (m + 1) := by
  interval_cases m <;> (simp only [← cMomentSum_eq]; native_decide)

/-- S_2 is monotone on verified resolutions: S_2(m) ≤ S_2(m+1) for m ≤ 6.
    prop:pom-s2-recurrence-mono-verified -/
theorem momentSum_two_mono_verified (m : Nat) (hm : m ≤ 6) :
    momentSum 2 m ≤ momentSum 2 (m + 1) :=
  Nat.le_of_lt (momentSum_two_strict_mono_verified m hm)

/-- S_3 is strictly increasing on verified resolutions: S_3(m) < S_3(m+1) for m ≤ 6.
    thm:pom-rank-exact-s3-strict-mono -/
theorem momentSum_three_strict_mono_verified (m : Nat) (hm : m ≤ 6) :
    momentSum 3 m < momentSum 3 (m + 1) := by
  interval_cases m <;> (simp only [← cMomentSum_eq]; native_decide)

/-- S_3 is monotone on verified resolutions: S_3(m) ≤ S_3(m+1) for m ≤ 6.
    prop:pom-s3-recurrence-mono-verified -/
theorem momentSum_three_mono_verified (m : Nat) (hm : m ≤ 6) :
    momentSum 3 m ≤ momentSum 3 (m + 1) :=
  Nat.le_of_lt (momentSum_three_strict_mono_verified m hm)

/-- S_2 resolution monotonicity, conditional on the universal recurrence:
    If S_2(m+3) + 2·S_2(m) = 2·S_2(m+2) + 2·S_2(m+1) for all m,
    then S_2(m) ≤ S_2(m+1) for all m.

    Proof: The recurrence gives S(m+3) = 2·S(m+2) + 2·S(m+1) − 2·S(m).
    If S(k) ≤ S(k+1) for all k < m, then S(m+1) − S(m) ≥ 0 implies
    S(m+3) ≥ 2·S(m+2) ≥ S(m+2).
    prop:pom-s2-recurrence-mono-of-recurrence -/
theorem momentSum_two_mono_of_recurrence
    (rec : ∀ m, momentSum 2 (m + 3) + 2 * momentSum 2 m =
      2 * momentSum 2 (m + 2) + 2 * momentSum 2 (m + 1))
    : ∀ m, momentSum 2 m ≤ momentSum 2 (m + 1) := by
  -- Prove the stronger statement: ∀ m, S(m) ≤ S(m+1) ∧ S(m+1) ≤ S(m+2)
  suffices h : ∀ m, momentSum 2 m ≤ momentSum 2 (m + 1) ∧
    momentSum 2 (m + 1) ≤ momentSum 2 (m + 2) from fun m => (h m).1
  intro m
  induction m with
  | zero =>
    constructor
    · simp only [← cMomentSum_eq]; native_decide
    · simp only [← cMomentSum_eq]; native_decide
  | succ n ih =>
    have ih1 := ih.1  -- S(n) ≤ S(n+1)
    have ih2 := ih.2  -- S(n+1) ≤ S(n+2)
    refine ⟨ih2, ?_⟩
    -- Need: S(n+2) ≤ S(n+3)
    -- From recurrence at n: S(n+3) + 2·S(n) = 2·S(n+2) + 2·S(n+1)
    have hrec := rec n
    -- S(n+3) = 2·S(n+2) + 2·S(n+1) - 2·S(n) ≥ 2·S(n+2) ≥ S(n+2)
    -- omega sees: n+1+1 = n+2, n+1+2 = n+3 by definitional equality
    -- But we need to introduce the values at the right indices
    have h_eq1 : momentSum 2 (n + 1 + 1) = momentSum 2 (n + 2) := rfl
    have h_eq2 : momentSum 2 (n + 1 + 2) = momentSum 2 (n + 3) := rfl
    rw [h_eq1, h_eq2]
    omega

/-- S_3 resolution monotonicity, conditional on the universal recurrence.
    prop:pom-s3-recurrence-mono-of-recurrence -/
theorem momentSum_three_mono_of_recurrence
    (rec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1))
    : ∀ m, momentSum 3 m ≤ momentSum 3 (m + 1) := by
  suffices h : ∀ m, momentSum 3 m ≤ momentSum 3 (m + 1) ∧
    momentSum 3 (m + 1) ≤ momentSum 3 (m + 2) from fun m => (h m).1
  intro m
  induction m with
  | zero =>
    constructor
    · simp only [← cMomentSum_eq]; native_decide
    · simp only [← cMomentSum_eq]; native_decide
  | succ n ih =>
    have ih1 := ih.1
    have ih2 := ih.2
    refine ⟨ih2, ?_⟩
    have hrec := rec n
    have h_eq1 : momentSum 3 (n + 1 + 1) = momentSum 3 (n + 2) := rfl
    have h_eq2 : momentSum 3 (n + 1 + 2) = momentSum 3 (n + 3) := rfl
    rw [h_eq1, h_eq2]
    omega

/-! ### Normalized Hankel matrix (S_2(n+2)/2 normalization)

The sequence a_n = S_2(n+2)/2 has values 3, 7, 18, 44, 110, ... -/

/-- The 3×3 Hankel matrix for the normalized sequence a_n = S_2(n+2)/2:
    [[3,7,18],[7,18,44],[18,44,110]]. -/
def hankelS2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![3, 7, 18; 7, 18, 44; 18, 44, 110]

/-- The determinant of the normalized Hankel matrix is −2. -/
theorem hankelS2_det : hankelS2.det = -2 := by native_decide

/-- The normalized Hankel determinant is nonzero. -/
theorem hankelS2_det_ne_zero : hankelS2.det ≠ 0 := by rw [hankelS2_det]; decide

/-- The 4×4 normalized Hankel matrix for S_2 (a_n = S_2(n+2)/2):
    [[3,7,18,44],[7,18,44,110],[18,44,110,272],[44,110,272,676]].
    a_6 = S_2(8)/2 = 1352/2 = 676. -/
def hankelS2_norm_4x4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![3, 7, 18, 44; 7, 18, 44, 110; 18, 44, 110, 272; 44, 110, 272, 676]

/-- The normalized 4×4 Hankel determinant for S_2 is 0.
    lem:pom-s2-hankel-norm-4x4 -/
theorem hankelS2_norm_4x4_det : hankelS2_norm_4x4.det = 0 := by native_decide

/-- The minimal recurrence order for the normalized S_2 sequence is 3:
    3×3 Hankel nonsingular, 4×4 Hankel singular.
    lem:pom-s2-rank-exact-three -/
theorem hankelS2_rank_exact_three : hankelS2.det ≠ 0 ∧ hankelS2_norm_4x4.det = 0 :=
  ⟨hankelS2_det_ne_zero, hankelS2_norm_4x4_det⟩

/-! ### Normalized Hankel matrix for S_3 -/

/-- The 3×3 Hankel matrix for the normalized sequence b_n = S_3(n+2)/2:
    [[5,13,44],[13,44,130],[44,130,410]]. -/
def hankelS3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![5, 13, 44; 13, 44, 130; 44, 130, 410]

/-- The determinant of the normalized S_3 Hankel matrix is −54.
    lem:pom-s3-hankel-normalized -/
theorem hankelS3_det : hankelS3.det = -54 := by native_decide

/-- The normalized S_3 Hankel determinant is nonzero.
    lem:pom-s3-hankel-normalized-nonzero -/
theorem hankelS3_det_ne_zero : hankelS3.det ≠ 0 := by rw [hankelS3_det]; decide

/-- S_2 does not satisfy any second-order linear recurrence over the verified range.
    Proof: if d·S_2(m+1) = α·S_2(m) + β·S_2(m−1) held for m = 2..4, then
    the system at m = 2,3 forces 2α = 3d, but m = 4 forces 3α = 5d,
    yielding d = 0, contradicting d ≠ 0. -/
theorem momentSum_two_no_second_order_recurrence :
    ¬ ∃ (α β d : ℤ), d ≠ 0 ∧
      d * (momentSum 2 3 : ℤ) = α * momentSum 2 2 + β * momentSum 2 1 ∧
      d * (momentSum 2 4 : ℤ) = α * momentSum 2 3 + β * momentSum 2 2 ∧
      d * (momentSum 2 5 : ℤ) = α * momentSum 2 4 + β * momentSum 2 3 := by
  simp only [momentSum_two_one, momentSum_two_two, momentSum_two_three,
    momentSum_two_four, momentSum_two_five]
  intro ⟨α, β, d, hd, h1, h2, h3⟩
  -- h1 : d * 14 = α * 6 + β * 2
  -- h2 : d * 36 = α * 14 + β * 6
  -- h3 : d * 88 = α * 36 + β * 14
  omega

/-! ### S_2 resolution monotonicity (explicit conjunction) -/

/-- S_2 is monotonically increasing across verified resolutions 0..7.
    thm:pom-s2-mono-resolution-verified -/
theorem momentSum_two_mono_resolution_verified :
    (momentSum 2 0 ≤ momentSum 2 1) ∧
    (momentSum 2 1 ≤ momentSum 2 2) ∧
    (momentSum 2 2 ≤ momentSum 2 3) ∧
    (momentSum 2 3 ≤ momentSum 2 4) ∧
    (momentSum 2 4 ≤ momentSum 2 5) ∧
    (momentSum 2 5 ≤ momentSum 2 6) ∧
    (momentSum 2 6 ≤ momentSum 2 7) := by
  simp only [momentSum_two_zero, momentSum_two_one, momentSum_two_two,
    momentSum_two_three, momentSum_two_four, momentSum_two_five,
    momentSum_two_six, momentSum_two_seven]
  omega

/-- S_3 is monotonically increasing across verified resolutions 0..7.
    thm:pom-s3-mono-resolution-verified -/
theorem momentSum_three_mono_resolution_verified :
    (momentSum 3 0 ≤ momentSum 3 1) ∧
    (momentSum 3 1 ≤ momentSum 3 2) ∧
    (momentSum 3 2 ≤ momentSum 3 3) ∧
    (momentSum 3 3 ≤ momentSum 3 4) ∧
    (momentSum 3 4 ≤ momentSum 3 5) ∧
    (momentSum 3 5 ≤ momentSum 3 6) ∧
    (momentSum 3 6 ≤ momentSum 3 7) := by
  simp only [momentSum_three_zero, momentSum_three_one, momentSum_three_two,
    momentSum_three_three, momentSum_three_four, momentSum_three_five,
    momentSum_three_six, momentSum_three_seven]
  omega

/-- Paper label: S_2 Hankel rank is exactly 3.
    thm:pom-s2-rank-exact -/
theorem paper_s2_hankel_rank_exact :
    hankelS2_3x3.det ≠ 0 ∧ hankelS2_4x4.det = 0 :=
  momentSum_two_minimal_recurrence_order

/-- Paper label: S_2 Hankel 3×3 determinant.
    lem:pom-s2-hankel-det -/
theorem paper_s2_hankel_det :
    hankelS2_3x3.det = -4 ∧ hankelS2_3x3.det ≠ 0 :=
  ⟨hankelS2_3x3_det, hankelS2_3x3_det_ne_zero⟩

end Omega
