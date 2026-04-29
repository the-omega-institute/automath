import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

private lemma pom_replica_softcore_fibonacci_power_moment_collapse_mode_identity
    (m : ℕ) :
    (1 + 2 / Real.sqrt 5) * Real.goldenRatio ^ m +
        (1 - 2 / Real.sqrt 5) * Real.goldenConj ^ m =
      (Nat.fib (m + 3) : ℝ) := by
  have hsqrt_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by norm_num
  rw [Real.coe_fib_eq]
  field_simp [hsqrt_ne]
  rw [← Real.goldenRatio_sub_goldenConj]
  have hphi3 :
      Real.goldenRatio ^ (3 : ℕ) = Real.goldenRatio - Real.goldenConj + 2 := by
    rw [Real.goldenRatio, Real.goldenConj]
    ring_nf
    have hsqrt_cube : (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = (Real.sqrt 5) ^ (2 : ℕ) * Real.sqrt 5 := by
          ring
        _ = 5 * Real.sqrt 5 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    rw [hsqrt_cube]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  have hpsi3 :
      Real.goldenConj ^ (3 : ℕ) = 2 - (Real.goldenRatio - Real.goldenConj) := by
    rw [Real.goldenRatio, Real.goldenConj]
    ring_nf
    have hsqrt_cube : (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5 : ℝ) ^ (3 : ℕ) = (Real.sqrt 5) ^ (2 : ℕ) * Real.sqrt 5 := by
          ring
        _ = 5 * Real.sqrt 5 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    rw [hsqrt_cube]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  rw [show Real.goldenRatio ^ (m + 3) = Real.goldenRatio ^ m * Real.goldenRatio ^ (3 : ℕ) by
      rw [← pow_add], show Real.goldenConj ^ (m + 3) =
        Real.goldenConj ^ m * Real.goldenConj ^ (3 : ℕ) by rw [← pow_add]]
  rw [hphi3, hpsi3]
  ring

private lemma pom_replica_softcore_fibonacci_power_moment_collapse_binomial
    (q m : ℕ) :
    (∑ i : Fin (q + 1),
        ((Nat.choose q i.1 : ℝ) * (1 + 2 / Real.sqrt 5) ^ (q - i.1) *
            (1 - 2 / Real.sqrt 5) ^ i.1) *
          (((1 / 2 : ℝ) * Real.goldenRatio ^ (q - i.1) *
              Real.goldenConj ^ i.1) ^ m)) =
      (1 / 2 : ℝ) ^ m *
        (((1 + 2 / Real.sqrt 5) * Real.goldenRatio ^ m +
          (1 - 2 / Real.sqrt 5) * Real.goldenConj ^ m) ^ q) := by
  let A : ℝ := (1 + 2 / Real.sqrt 5) * Real.goldenRatio ^ m
  let B : ℝ := (1 - 2 / Real.sqrt 5) * Real.goldenConj ^ m
  let F : ℕ → ℝ := fun i =>
    ((Nat.choose q i : ℝ) * (1 + 2 / Real.sqrt 5) ^ (q - i) *
        (1 - 2 / Real.sqrt 5) ^ i) *
      (((1 / 2 : ℝ) * Real.goldenRatio ^ (q - i) * Real.goldenConj ^ i) ^ m)
  change (∑ i : Fin (q + 1), F i.1) =
    (1 / 2 : ℝ) ^ m *
      (((1 + 2 / Real.sqrt 5) * Real.goldenRatio ^ m +
        (1 - 2 / Real.sqrt 5) * Real.goldenConj ^ m) ^ q)
  rw [Fin.sum_univ_eq_sum_range]
  calc
    (∑ i ∈ Finset.range (q + 1),
        ((Nat.choose q i : ℝ) * (1 + 2 / Real.sqrt 5) ^ (q - i) *
            (1 - 2 / Real.sqrt 5) ^ i) *
          (((1 / 2 : ℝ) * Real.goldenRatio ^ (q - i) * Real.goldenConj ^ i) ^ m)) =
        (∑ i ∈ Finset.range (q + 1), (1 / 2 : ℝ) ^ m * (B ^ i * A ^ (q - i) *
          (Nat.choose q i : ℝ))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp only [A, B]
      rw [mul_pow, mul_pow]
      rw [show (Real.goldenRatio ^ (q - i)) ^ m =
          (Real.goldenRatio ^ m) ^ (q - i) by
        rw [pow_right_comm]]
      rw [show (Real.goldenConj ^ i) ^ m = (Real.goldenConj ^ m) ^ i by
        rw [pow_right_comm]]
      simp only [mul_pow]
      ring
    _ = (1 / 2 : ℝ) ^ m *
        (∑ i ∈ Finset.range (q + 1), B ^ i * A ^ (q - i) * (Nat.choose q i : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) ^ m * (A + B) ^ q := by
      rw [add_comm A B, add_pow]
    _ = (1 / 2 : ℝ) ^ m *
        (((1 + 2 / Real.sqrt 5) * Real.goldenRatio ^ m +
          (1 - 2 / Real.sqrt 5) * Real.goldenConj ^ m) ^ q) := by
      rfl

/-- Paper label: `thm:pom-replica-softcore-fibonacci-power-moment-collapse`. -/
theorem paper_pom_replica_softcore_fibonacci_power_moment_collapse (q m : ℕ) :
    (2 : ℝ) ^ m * (∑ i : Fin (q + 1),
      ((Nat.choose q i.1 : ℝ) * (1 + 2 / Real.sqrt 5) ^ (q - i.1) *
        (1 - 2 / Real.sqrt 5) ^ i.1) *
        (((1 / 2 : ℝ) * Real.goldenRatio ^ (q - i.1) *
          Real.goldenConj ^ i.1) ^ m)) = (Nat.fib (m + 3) : ℝ) ^ q := by
  rw [pom_replica_softcore_fibonacci_power_moment_collapse_binomial,
    pom_replica_softcore_fibonacci_power_moment_collapse_mode_identity]
  have hpow : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hpow, one_mul]

/-- The geometric node appearing in the Fibonacci-power moment expansion. -/
noncomputable def pom_replica_softcore_fibonacci_power_hankel_determinant_node
    (q : ℕ) (i : Fin (q + 1)) : ℝ :=
  Real.goldenRatio ^ (q - i.1) * Real.goldenConj ^ i.1

/-- The binomial weight attached to a geometric node. -/
noncomputable def pom_replica_softcore_fibonacci_power_hankel_determinant_weight
    (q : ℕ) (i : Fin (q + 1)) : ℝ :=
  (Nat.choose q i.1 : ℝ) * (1 + 2 / Real.sqrt 5) ^ (q - i.1) *
    (1 - 2 / Real.sqrt 5) ^ i.1

/-- The Hankel matrix of the finite geometric moment expansion for `F_{n+3}^q`. -/
noncomputable def pom_replica_softcore_fibonacci_power_hankel_determinant_hankel
    (q : ℕ) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  fun i j =>
    ∑ k : Fin (q + 1),
      pom_replica_softcore_fibonacci_power_hankel_determinant_weight q k *
        pom_replica_softcore_fibonacci_power_hankel_determinant_node q k ^ (i.1 + j.1)

lemma pom_replica_softcore_fibonacci_power_hankel_determinant_vandermonde_factorization
    (q : ℕ) :
    pom_replica_softcore_fibonacci_power_hankel_determinant_hankel q =
      Matrix.transpose
          (Matrix.vandermonde
            (pom_replica_softcore_fibonacci_power_hankel_determinant_node q)) *
        Matrix.diagonal
          (pom_replica_softcore_fibonacci_power_hankel_determinant_weight q) *
        Matrix.vandermonde
          (pom_replica_softcore_fibonacci_power_hankel_determinant_node q) := by
  ext i j
  simp [pom_replica_softcore_fibonacci_power_hankel_determinant_hankel,
    Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.diagonal, pow_add]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hki : k = i <;> simp [hki, mul_assoc, mul_left_comm, mul_comm]

lemma pom_replica_softcore_fibonacci_power_hankel_determinant_det_factorization
    (q : ℕ) :
    (pom_replica_softcore_fibonacci_power_hankel_determinant_hankel q).det =
      (∏ k : Fin (q + 1),
          pom_replica_softcore_fibonacci_power_hankel_determinant_weight q k) *
        (∏ i : Fin (q + 1),
          ∏ j ∈ Finset.Ioi i,
            (pom_replica_softcore_fibonacci_power_hankel_determinant_node q j -
              pom_replica_softcore_fibonacci_power_hankel_determinant_node q i)) ^ 2 := by
  rw [pom_replica_softcore_fibonacci_power_hankel_determinant_vandermonde_factorization]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Matrix.det_vandermonde]
  ring

/-- Paper-facing determinant package: the Hankel matrix of the finite Fibonacci-power geometric
moment expansion factors as `Vᵀ C V`, hence its determinant is the squared Vandermonde product
times the product of the binomial weights. -/
def pom_replica_softcore_fibonacci_power_hankel_determinant_statement : Prop :=
  ∀ q : ℕ,
    (pom_replica_softcore_fibonacci_power_hankel_determinant_hankel q).det =
      (∏ k : Fin (q + 1),
          pom_replica_softcore_fibonacci_power_hankel_determinant_weight q k) *
        (∏ i : Fin (q + 1),
          ∏ j ∈ Finset.Ioi i,
            (pom_replica_softcore_fibonacci_power_hankel_determinant_node q j -
              pom_replica_softcore_fibonacci_power_hankel_determinant_node q i)) ^ 2

/-- Paper label:
`thm:pom-replica-softcore-fibonacci-power-hankel-determinant`. -/
theorem paper_pom_replica_softcore_fibonacci_power_hankel_determinant :
    pom_replica_softcore_fibonacci_power_hankel_determinant_statement := by
  intro q
  exact pom_replica_softcore_fibonacci_power_hankel_determinant_det_factorization q

end

end Omega.POM
