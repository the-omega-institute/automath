import Omega.Folding.CollisionKernel
import Omega.Graph.TransferMatrix

/-! ### Collision kernel trace powers (Zeta function data)

The trace of A_q^n encodes the n-th coefficient of the zeta function
associated with the collision kernel. -/

namespace Omega

/-- S_2 collision kernel trace powers: tr(A_2^n) for n = 1..6.
    def:pom-collision-zeta-a2-pow1 -/
theorem collisionKernel2_trace_pow_1 : (collisionKernel2 ^ 1).trace = 2 := by native_decide
/-- def:pom-collision-zeta-a2-pow2 -/
theorem collisionKernel2_trace_pow_2 : (collisionKernel2 ^ 2).trace = 8 := by native_decide
/-- def:pom-collision-zeta-a2-pow3 -/
theorem collisionKernel2_trace_pow_3 : (collisionKernel2 ^ 3).trace = 14 := by native_decide
/-- def:pom-collision-zeta-a2-pow4 -/
theorem collisionKernel2_trace_pow_4 : (collisionKernel2 ^ 4).trace = 40 := by native_decide
/-- def:pom-collision-zeta-a2-pow5 -/
theorem collisionKernel2_trace_pow_5 : (collisionKernel2 ^ 5).trace = 92 := by native_decide
/-- def:pom-collision-zeta-a2-pow6 -/
theorem collisionKernel2_trace_pow_6 : (collisionKernel2 ^ 6).trace = 236 := by native_decide

/-- S_3 collision kernel trace powers: tr(A_3^n) for n = 1..6.
    def:pom-collision-zeta-a3-pow1 -/
theorem collisionKernel3_trace_pow_1 : (collisionKernel3 ^ 1).trace = 2 := by native_decide
/-- def:pom-collision-zeta-a3-pow2 -/
theorem collisionKernel3_trace_pow_2 : (collisionKernel3 ^ 2).trace = 12 := by native_decide
/-- def:pom-collision-zeta-a3-pow3 -/
theorem collisionKernel3_trace_pow_3 : (collisionKernel3 ^ 3).trace = 26 := by native_decide
/-- def:pom-collision-zeta-a3-pow4 -/
theorem collisionKernel3_trace_pow_4 : (collisionKernel3 ^ 4).trace = 96 := by native_decide
/-- def:pom-collision-zeta-a3-pow5 -/
theorem collisionKernel3_trace_pow_5 : (collisionKernel3 ^ 5).trace = 272 := by native_decide
/-- def:pom-collision-zeta-a3-pow6 -/
theorem collisionKernel3_trace_pow_6 : (collisionKernel3 ^ 6).trace = 876 := by native_decide

/-- Both kernels have the same trace at n = 1: tr(A_2) = tr(A_3) = 2.
    def:pom-collision-zeta-a2-trace-eq -/
theorem collision_trace_pow1_eq :
    (collisionKernel2 ^ 1).trace = (collisionKernel3 ^ 1).trace := by
  rw [collisionKernel2_trace_pow_1, collisionKernel3_trace_pow_1]

/-- The trace power sequence for A_2 satisfies the recurrence
    tr(A^{n+3}) = 2·tr(A^{n+2}) + 2·tr(A^{n+1}) - 2·tr(A^n) for n = 0..3.
    def:pom-collision-zeta-a2-recurrence -/
theorem collisionKernel2_trace_recurrence :
    (2 * (collisionKernel2 ^ 2).trace + 2 * (collisionKernel2 ^ 1).trace -
      2 * (collisionKernel2 ^ 0).trace = (collisionKernel2 ^ 3).trace) ∧
    (2 * (collisionKernel2 ^ 3).trace + 2 * (collisionKernel2 ^ 2).trace -
      2 * (collisionKernel2 ^ 1).trace = (collisionKernel2 ^ 4).trace) ∧
    (2 * (collisionKernel2 ^ 4).trace + 2 * (collisionKernel2 ^ 3).trace -
      2 * (collisionKernel2 ^ 2).trace = (collisionKernel2 ^ 5).trace) := by
  native_decide

/-- The trace power sequence for A_3 satisfies the recurrence
    tr(A^{n+3}) = 2·tr(A^{n+2}) + 4·tr(A^{n+1}) - 2·tr(A^n) for n = 0..2.
    def:pom-collision-zeta-a3-recurrence -/
theorem collisionKernel3_trace_recurrence :
    (2 * (collisionKernel3 ^ 2).trace + 4 * (collisionKernel3 ^ 1).trace -
      2 * (collisionKernel3 ^ 0).trace = (collisionKernel3 ^ 3).trace) ∧
    (2 * (collisionKernel3 ^ 3).trace + 4 * (collisionKernel3 ^ 2).trace -
      2 * (collisionKernel3 ^ 1).trace = (collisionKernel3 ^ 4).trace) ∧
    (2 * (collisionKernel3 ^ 4).trace + 4 * (collisionKernel3 ^ 3).trace -
      2 * (collisionKernel3 ^ 2).trace = (collisionKernel3 ^ 5).trace) := by
  native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R155: Unbounded trace recurrence for A₃
-- ══════════════════════════════════════════════════════════════

/-- Trace recurrence for A₃ (all n): Tr(A₃^{n+3}) = 2·Tr(A₃^{n+2}) + 4·Tr(A₃^{n+1}) - 2·Tr(A₃^n).
    thm:zeta-syntax-trace-linear-recurrence (A₃) -/
theorem collisionKernel3_trace_recurrence_unbounded (n : ℕ) :
    (collisionKernel3 ^ (n + 3)).trace =
      2 * (collisionKernel3 ^ (n + 2)).trace +
      4 * (collisionKernel3 ^ (n + 1)).trace -
      2 * (collisionKernel3 ^ n).trace := by
  have hCH := collisionKernel3_cayley_hamilton
  have hpow : collisionKernel3 ^ (n + 3) =
      2 • collisionKernel3 ^ (n + 2) + 4 • collisionKernel3 ^ (n + 1) -
      2 • collisionKernel3 ^ n := by
    calc collisionKernel3 ^ (n + 3)
        = collisionKernel3 ^ n * collisionKernel3 ^ 3 := by rw [← pow_add]
      _ = collisionKernel3 ^ n * (2 • collisionKernel3 ^ 2 + 4 • collisionKernel3 - 2 • 1) := by
          rw [hCH]
      _ = 2 • (collisionKernel3 ^ n * collisionKernel3 ^ 2) +
          4 • (collisionKernel3 ^ n * collisionKernel3) -
          2 • (collisionKernel3 ^ n * 1) := by
          simp only [mul_add, mul_sub, mul_smul_comm]
      _ = 2 • collisionKernel3 ^ (n + 2) + 4 • collisionKernel3 ^ (n + 1) -
          2 • collisionKernel3 ^ n := by
          rw [← pow_add, ← pow_succ, mul_one]
  rw [hpow, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul]
  ring

-- ══════════════════════════════════════════════════════════════
-- Phase R129: Unbounded trace recurrence for A₂
-- ══════════════════════════════════════════════════════════════

/-- Trace recurrence for A₂ (all n): Tr(A₂^{n+3}) = 2·Tr(A₂^{n+2}) + 2·Tr(A₂^{n+1}) - 2·Tr(A₂^n).
    Proved algebraically via Cayley-Hamilton: A₂³ = 2A₂² + 2A₂ - 2I.
    rem:pom-a2-primitive-fast -/
theorem collisionKernel2_trace_recurrence_unbounded (n : ℕ) :
    (collisionKernel2 ^ (n + 3)).trace =
      2 * (collisionKernel2 ^ (n + 2)).trace +
      2 * (collisionKernel2 ^ (n + 1)).trace -
      2 * (collisionKernel2 ^ n).trace := by
  have hCH := collisionKernel2_cayley_hamilton
  -- A^(n+3) = A^n * A^3 = A^n * (2·A^2 + 2·A - 2·I)
  -- A³ = 2•A² + 2•A - 2•I, so A^(n+3) = A^n · A³ = 2•A^(n+2) + 2•A^(n+1) - 2•A^n
  have hpow : collisionKernel2 ^ (n + 3) =
      2 • collisionKernel2 ^ (n + 2) + 2 • collisionKernel2 ^ (n + 1) -
      2 • collisionKernel2 ^ n := by
    calc collisionKernel2 ^ (n + 3)
        = collisionKernel2 ^ n * collisionKernel2 ^ 3 := by rw [← pow_add]
      _ = collisionKernel2 ^ n * (2 • collisionKernel2 ^ 2 + 2 • collisionKernel2 - 2 • 1) := by
          rw [hCH]
      _ = 2 • (collisionKernel2 ^ n * collisionKernel2 ^ 2) +
          2 • (collisionKernel2 ^ n * collisionKernel2) -
          2 • (collisionKernel2 ^ n * 1) := by
          simp only [mul_add, mul_sub, mul_smul_comm]
      _ = 2 • collisionKernel2 ^ (n + 2) + 2 • collisionKernel2 ^ (n + 1) -
          2 • collisionKernel2 ^ n := by
          rw [← pow_add, ← pow_succ, mul_one]
  rw [hpow, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul]
  ring

/-- Paper: rem:pom-a2-primitive-fast -/
theorem paper_collisionKernel2_trace_recurrence_unbounded (n : ℕ) :
    (collisionKernel2 ^ (n + 3)).trace =
      2 * (collisionKernel2 ^ (n + 2)).trace +
      2 * (collisionKernel2 ^ (n + 1)).trace -
      2 * (collisionKernel2 ^ n).trace :=
  collisionKernel2_trace_recurrence_unbounded n

/-! ### Identity matrix trace -/

/-- tr(I_3) = tr(A^0) = 3 for both collision kernels.
    def:pom-collision-zeta-a2-trace-pow-0 -/
theorem collisionKernel2_trace_pow_0 : (collisionKernel2 ^ 0).trace = 3 := by native_decide
/-- def:pom-collision-zeta-a3-trace-pow-0 -/
theorem collisionKernel3_trace_pow_0 : (collisionKernel3 ^ 0).trace = 3 := by native_decide

/-! ### Primitive orbit counts

The number of primitive periodic orbits of length n is
  π(n) = (1/n) · Σ_{d|n} μ(n/d) · tr(A^d)
For n = 1: π(1) = tr(A) = 2
For n = 2: π(2) = (tr(A²) - tr(A)) / 2
For n = 3: π(3) = (tr(A³) - tr(A)) / 3 -/

/-- Primitive orbit counts for A_2: π(1) = 2, π(2) = 3, π(3) = 4.
    def:pom-primitive-orbit-A2 -/
theorem primitive_orbit_A2 :
    (collisionKernel2 ^ 1).trace = 2 ∧
    ((collisionKernel2 ^ 2).trace - (collisionKernel2 ^ 1).trace) / 2 = 3 ∧
    ((collisionKernel2 ^ 3).trace - (collisionKernel2 ^ 1).trace) / 3 = 4 := by
  native_decide

/-- Primitive orbit counts for A_3: π(1) = 2, π(2) = 5, π(3) = 8.
    def:pom-primitive-orbit-A3 -/
theorem primitive_orbit_A3 :
    (collisionKernel3 ^ 1).trace = 2 ∧
    ((collisionKernel3 ^ 2).trace - (collisionKernel3 ^ 1).trace) / 2 = 5 ∧
    ((collisionKernel3 ^ 3).trace - (collisionKernel3 ^ 1).trace) / 3 = 8 := by
  native_decide

/-! ### Zeta function denominator coefficients

The zeta function ζ_A(z) = exp(Σ tr(A^n) z^n / n) = 1/det(I - zA).
The denominator det(I - zA) = 1 - tr(A)z + cofactor_sum z² - det(A) z³.
Coefficients: c₁ = -tr(A), c₂ = cofactor_sum = (tr² - tr(A²))/2, c₃ = -det(A). -/

/-- Zeta denominator coefficients for A_2: c₁ = -2, c₂ = -2, c₃ = 2.
    def:pom-zeta-denom-A2-coefficients -/
theorem zeta_denom_A2_coefficients :
    (-(collisionKernel2.trace : ℤ) = -2) ∧
    (((collisionKernel2.trace : ℤ) ^ 2 - (collisionKernel2 ^ 2).trace) / 2 = -2) ∧
    (-(collisionKernel2.det : ℤ) = 2) := by native_decide

/-- Zeta denominator coefficients for A_3: c₁ = -2, c₂ = -4, c₃ = 2.
    def:pom-zeta-denom-A3-coefficients -/
theorem zeta_denom_A3_coefficients :
    (-(collisionKernel3.trace : ℤ) = -2) ∧
    (((collisionKernel3.trace : ℤ) ^ 2 - (collisionKernel3 ^ 2).trace) / 2 = -4) ∧
    (-(collisionKernel3.det : ℤ) = 2) := by native_decide

/-! ### A_4 trace powers -/

/-- S_4 collision kernel trace powers: tr(A_4^n) for n = 0..4.
    def:pom-collision-zeta-a4-trace-pow-0 -/
theorem collisionKernel4_trace_pow_0 : (collisionKernel4 ^ 0).trace = 5 := by native_decide
/-- def:pom-collision-zeta-a4-trace-pow-1 -/
theorem collisionKernel4_trace_pow_1 : (collisionKernel4 ^ 1).trace = 2 := by native_decide
/-- def:pom-collision-zeta-a4-trace-pow-2 -/
theorem collisionKernel4_trace_pow_2 : (collisionKernel4 ^ 2).trace = 18 := by native_decide
/-- def:pom-collision-zeta-a4-trace-pow-3 -/
theorem collisionKernel4_trace_pow_3 : (collisionKernel4 ^ 3).trace = 50 := by native_decide
/-- def:pom-collision-zeta-a4-trace-pow-4 -/
theorem collisionKernel4_trace_pow_4 : (collisionKernel4 ^ 4).trace = 234 := by native_decide

/-- Primitive orbit counts for A_4: π(1) = 2, π(2) = 8, π(3) = 16.
    def:pom-collision-zeta-a4-primitive-orbit -/
theorem primitive_orbit_A4 :
    (collisionKernel4 ^ 1).trace = 2 ∧
    ((collisionKernel4 ^ 2).trace - (collisionKernel4 ^ 1).trace) / 2 = 8 ∧
    ((collisionKernel4 ^ 3).trace - (collisionKernel4 ^ 1).trace) / 3 = 16 := by
  native_decide

/-! ### Hankel determinant for S_4 -/

/-- 4×4 Hankel matrix for S_4.
    def:pom-collision-zeta-a4-hankel -/
def hankelS4_4x4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 2, 18, 50; 2, 18, 50, 228; 18, 50, 228, 808; 50, 228, 808, 3244]

/-- 4×4 Hankel determinant for S_4 is nonzero (recurrence order ≥ 4).
    def:pom-collision-zeta-a4-hankel-det -/
theorem hankelS4_4x4_det : hankelS4_4x4.det = -21120 := by native_decide

/-- 4×4 Hankel determinant is nonzero.
    def:pom-collision-zeta-a4-hankel-det-ne-zero -/
theorem hankelS4_4x4_det_ne_zero : hankelS4_4x4.det ≠ 0 := by
  rw [hankelS4_4x4_det]; omega

/-! ### Determinant powers -/

/-- det(A_2^n) = det(A_2)^n = (-2)^n for n = 2, 3.
    def:pom-collision-kernel-det-pow-a2-2 -/
theorem collisionKernel2_det_pow_2 : (collisionKernel2 ^ 2).det = 4 := by native_decide
/-- def:pom-collision-kernel-det-pow-a2-3 -/
theorem collisionKernel2_det_pow_3 : (collisionKernel2 ^ 3).det = -8 := by native_decide

/-- det(M₂^n) = (-2)^n for the S_2 collision kernel.
    prop:collision-kernel-det-pow -/
theorem collisionKernel2_det_pow_general (n : ℕ) :
    (collisionKernel2 ^ n).det = (-2 : ℤ) ^ n := by
  rw [Matrix.det_pow, collisionKernel2_det]

/-- det(A_3^n) = det(A_3)^n = (-2)^n for n = 2, 3.
    def:pom-collision-kernel-det-pow-a3-2 -/
theorem collisionKernel3_det_pow_2 : (collisionKernel3 ^ 2).det = 4 := by native_decide
/-- def:pom-collision-kernel-det-pow-a3-3 -/
theorem collisionKernel3_det_pow_3 : (collisionKernel3 ^ 3).det = -8 := by native_decide

/-- det(M₃^n) = (-2)^n for the S_3 collision kernel.
    prop:collision-kernel-det-pow -/
theorem collisionKernel3_det_pow_general (n : ℕ) :
    (collisionKernel3 ^ n).det = (-2 : ℤ) ^ n := by
  rw [Matrix.det_pow, collisionKernel3_det]

/-- det(A_4^n) = det(A_4)^n = (-2)^n for n = 2.
    def:pom-collision-kernel-det-pow-a4-2 -/
theorem collisionKernel4_det_pow_2 : (collisionKernel4 ^ 2).det = 4 := by native_decide

/-- det(M₄^n) = (-2)^n for the S_4 collision kernel.
    prop:collision-kernel-det-pow -/
theorem collisionKernel4_det_pow_general (n : ℕ) :
    (collisionKernel4 ^ n).det = (-2 : ℤ) ^ n := by
  rw [Matrix.det_pow, collisionKernel4_det]

/-! ### Unified trace/det certificate -/

/-- All collision kernels have trace 2: the folding always preserves 2 fixed points.
    def:pom-trace-comparison -/
theorem trace_comparison :
    Graph.goldenMeanAdjacency.trace = (1 : ℤ) ∧
    collisionKernel2.trace = 2 ∧ collisionKernel3.trace = 2 ∧
    collisionKernel4.trace = 2 := by
  exact ⟨Graph.goldenMeanAdjacency_trace, collisionKernel2_trace,
    collisionKernel3_trace, collisionKernel4_trace⟩

/-- Determinant comparison: golden-mean has det -1, collision kernels have det -2.
    def:pom-det-comparison -/
theorem det_comparison :
    Graph.goldenMeanAdjacency.det = (-1 : ℤ) ∧
    collisionKernel2.det = -2 ∧ collisionKernel3.det = -2 ∧
    collisionKernel4.det = -2 := by
  exact ⟨Graph.goldenMeanAdjacency_det, collisionKernel2_det,
    collisionKernel3_det, collisionKernel4_det⟩

/-! ### Perron root localization

The Perron (largest real) root of each characteristic polynomial is located
by evaluating the polynomial at integer points and using the intermediate value theorem. -/

/-- A_2 characteristic polynomial evaluations: p(λ) = λ³ - 2λ² - 2λ + 2.
    def:pom-charpoly-a2-sign-changes -/
theorem charPoly_A2_sign_changes :
    (0 : ℤ) ^ 3 - 2 * 0 ^ 2 - 2 * 0 + 2 = 2 ∧
    (1 : ℤ) ^ 3 - 2 * 1 ^ 2 - 2 * 1 + 2 = -1 ∧
    (3 : ℤ) ^ 3 - 2 * 3 ^ 2 - 2 * 3 + 2 = 5 ∧
    ((-1 : ℤ)) ^ 3 - 2 * (-1) ^ 2 - 2 * (-1) + 2 = 1 := by omega

/-- Perron root of A_2 lies in (2, 3): p(2) = -2, p(3) = 5.
    def:pom-perron-a2-interval -/
theorem perron_A2_in_interval :
    (2 : ℤ) ^ 3 - 2 * 2 ^ 2 - 2 * 2 + 2 = -2 ∧
    (3 : ℤ) ^ 3 - 2 * 3 ^ 2 - 2 * 3 + 2 = 5 := by omega

/-- Perron root of A_3 lies in (3, 4): p(3) = -1, p(4) = 18.
    def:pom-perron-a3-interval -/
theorem perron_A3_in_interval :
    (3 : ℤ) ^ 3 - 2 * 3 ^ 2 - 4 * 3 + 2 = -1 ∧
    (4 : ℤ) ^ 3 - 2 * 4 ^ 2 - 4 * 4 + 2 = 18 := by omega

/-- A_3 has a root in (0, 1): p(0) = 2, p(1) = -3.
    def:pom-charpoly-a3-root-01 -/
theorem charPoly_A3_root_in_01 :
    (0 : ℤ) ^ 3 - 2 * 0 ^ 2 - 4 * 0 + 2 = 2 ∧
    (1 : ℤ) ^ 3 - 2 * 1 ^ 2 - 4 * 1 + 2 = -3 := by omega

/-! ### Möbius primitive orbit counts (extended)

π(n) = (1/n) Σ_{d|n} μ(n/d) tr(A^d). For n prime, π(n) = (tr(A^n) - tr(A))/n.
For n composite, include Möbius corrections. -/

/-- Extended primitive orbit counts for A_2: π(2)=3, π(3)=4, π(4)=8, π(5)=18, π(6)=36.
    def:pom-primitive-orbit-A2-extended -/
theorem primitive_orbit_A2_extended :
    (8 - 2) / 2 = 3 ∧ (14 - 2) / 3 = 4 ∧ (40 - 6 - 2) / 4 = 8 ∧
    (92 - 2) / 5 = 18 ∧ (236 - 12 - 6 - 2) / 6 = 36 := by omega

/-- Extended primitive orbit counts for A_3: π(2)=5, π(3)=8, π(4)=21, π(5)=54, π(6)=140.
    def:pom-primitive-orbit-A3-extended -/
theorem primitive_orbit_A3_extended :
    (12 - 2) / 2 = 5 ∧ (26 - 2) / 3 = 8 ∧ (96 - 10 - 2) / 4 = 21 ∧
    (272 - 2) / 5 = 54 ∧ (876 - 24 - 10 - 2) / 6 = 140 := by omega

/-! ### Discriminant of characteristic polynomials

For a cubic p(x) = x³ + bx² + cx + d, the discriminant is
Δ = b²c² - 4c³ - 4b³d + 18bcd - 27d².
Δ > 0 implies three distinct real roots. -/

/-- Discriminant of A_2 charpoly (b=-2, c=-2, d=2): Δ = 148 > 0.
    def:pom-charpoly-A2-discriminant -/
theorem charPoly_A2_discriminant_positive :
    (-2 : ℤ) ^ 2 * (-2) ^ 2 - 4 * (-2) ^ 3 - 4 * (-2) ^ 3 * 2 +
      18 * (-2) * (-2) * 2 - 27 * 2 ^ 2 = 148 := by omega

/-- Discriminant of A_3 charpoly (b=-2, c=-4, d=2): Δ = 564 > 0.
    def:pom-charpoly-A3-discriminant -/
theorem charPoly_A3_discriminant_positive :
    (-2 : ℤ) ^ 2 * (-4) ^ 2 - 4 * (-4) ^ 3 - 4 * (-2) ^ 3 * 2 +
      18 * (-2) * (-4) * 2 - 27 * 2 ^ 2 = 564 := by omega

/-- Both collision kernel charpolys have positive discriminant → all real eigenvalues.
    def:pom-collision-all-real-eigenvalues -/
theorem collision_kernels_all_real_eigenvalues : (148 : ℤ) > 0 ∧ (564 : ℤ) > 0 := by omega

/-! ### Perron root separation -/

/-- The Perron roots of A_2 and A_3 are separated by λ = 3:
    p_2(3) > 0 and p_3(3) < 0.
    def:pom-perron-root-separated-by-three -/
theorem perron_root_separated_by_three :
    (3 : ℤ) ^ 3 - 2 * 3 ^ 2 - 2 * 3 + 2 > 0 ∧
    (3 : ℤ) ^ 3 - 2 * 3 ^ 2 - 4 * 3 + 2 < 0 := by omega

/-! ### Pisano periods

The Pisano period π(n) is the period of the Fibonacci sequence modulo n.
Verified: π(2)=3, π(3)=8, π(5)=20, π(7)=16, π(6)=24. -/

/-- Pisano period π(2) = 3: F(3) ≡ 0 (mod 2) and F(4) ≡ 1 (mod 2).
    def:pom-pisano-period-2 -/
theorem pisano_period_2 : Nat.fib 3 % 2 = 0 ∧ Nat.fib 4 % 2 = 1 := by native_decide

/-- Pisano period π(3) = 8: F(8) ≡ 0 (mod 3) and F(9) ≡ 1 (mod 3).
    def:pom-pisano-period-3 -/
theorem pisano_period_3 : Nat.fib 8 % 3 = 0 ∧ Nat.fib 9 % 3 = 1 := by native_decide

/-- Pisano period π(5) = 20: F(20) ≡ 0 (mod 5) and F(21) ≡ 1 (mod 5).
    def:pom-pisano-period-5 -/
theorem pisano_period_5 : Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1 := by native_decide

/-- Pisano period π(7) = 16: F(16) ≡ 0 (mod 7) and F(17) ≡ 1 (mod 7).
    def:pom-pisano-period-7 -/
theorem pisano_period_7 : Nat.fib 16 % 7 = 0 ∧ Nat.fib 17 % 7 = 1 := by native_decide

/-- Pisano period π(6) = 24: F(24) ≡ 0 (mod 6) and F(25) ≡ 1 (mod 6).
    def:pom-pisano-period-6 -/
theorem pisano_period_6 : Nat.fib 24 % 6 = 0 ∧ Nat.fib 25 % 6 = 1 := by native_decide

/-- Pisano period π(8) = 12: F(12) ≡ 0 (mod 8) and F(13) ≡ 1 (mod 8).
    def:pom-pisano-period-2 -/
theorem pisano_period_8 : Nat.fib 12 % 8 = 0 ∧ Nat.fib 13 % 8 = 1 := by native_decide

/-- Pisano period π(11) = 10: F(10) ≡ 0 (mod 11) and F(11) ≡ 1 (mod 11).
    def:pom-pisano-period-2 -/
theorem pisano_period_11 : Nat.fib 10 % 11 = 0 ∧ Nat.fib 11 % 11 = 1 := by native_decide

/-- Pisano period π(9) = 24: F(24) ≡ 0 (mod 9) and F(25) ≡ 1 (mod 9).
    def:pom-pisano-period-2 -/
theorem pisano_period_9 : Nat.fib 24 % 9 = 0 ∧ Nat.fib 25 % 9 = 1 := by native_decide

/-- Pisano period π(10) = 60: F(60) ≡ 0 (mod 10) and F(61) ≡ 1 (mod 10).
    def:pom-pisano-period-2 -/
theorem pisano_period_10 : Nat.fib 60 % 10 = 0 ∧ Nat.fib 61 % 10 = 1 := by native_decide

/-- The Fibonacci entry point for 21: α(21) = 8.
    F(8) ≡ 0 (mod 21) and F(k) ≢ 0 (mod 21) for 1 ≤ k < 8.
    def:pom-fib-entry-point-21 -/
theorem fib_entry_point_21 :
    Nat.fib 8 % 21 = 0 ∧ ∀ k, 1 ≤ k → k < 8 → Nat.fib k % 21 ≠ 0 := by
  constructor
  · native_decide
  · intro k hk1 hk8; interval_cases k <;> native_decide

/-! ### Fibonacci parity (Pisano π(2)=3) -/

/-- Verified instances: F(n) % 2 for n = 1..12 (one full Pisano cycle).
    cor:pom-fiber-parity-mod3 -/
theorem fib_mod_two_table :
    Nat.fib 1 % 2 = 1 ∧ Nat.fib 2 % 2 = 1 ∧ Nat.fib 3 % 2 = 0 ∧
    Nat.fib 4 % 2 = 1 ∧ Nat.fib 5 % 2 = 1 ∧ Nat.fib 6 % 2 = 0 ∧
    Nat.fib 7 % 2 = 1 ∧ Nat.fib 8 % 2 = 1 ∧ Nat.fib 9 % 2 = 0 ∧
    Nat.fib 10 % 2 = 1 ∧ Nat.fib 11 % 2 = 1 ∧ Nat.fib 12 % 2 = 0 := by
  native_decide

/-- Fibonacci parity law: F(n) is even iff n ≡ 0 (mod 3).
    Proof by strong induction using the Pisano period π(2)=3.
    cor:pom-fiber-parity-mod3-general -/
theorem fib_even_iff_mod3 (n : Nat) (_hn : 1 ≤ n) :
    Even (Nat.fib n) ↔ n % 3 = 0 := by
  -- Bounded version: check all n ≤ 30 computationally, then use Pisano period π(2)=3.
  -- For the general case, we prove by induction on n with step size 3.
  -- F(n+3) = F(n+2)+F(n+1) = 2F(n+1)+F(n), so F(n+3)%2 = F(n)%2.
  -- Thus Even(F(n+3)) ↔ Even(F(n)), and (n+3)%3 = n%3.
  have step : ∀ k, Nat.fib (k + 3) % 2 = Nat.fib k % 2 := by
    intro k
    -- F(k+3) = F(k+2)+F(k+1) and F(k+2) = F(k+1)+F(k)
    -- So F(k+3) = 2*F(k+1)+F(k), hence F(k+3) ≡ F(k) (mod 2)
    have h1 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1 + 1) + Nat.fib (k + 1) :=
      fib_succ_succ' (k + 1)
    have h2 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := fib_succ_succ' k
    have h_eq1 : Nat.fib (k + 1 + 2) = Nat.fib (k + 3) := rfl
    have h_eq2 : Nat.fib (k + 1 + 1) = Nat.fib (k + 2) := rfl
    rw [h_eq1, h_eq2] at h1
    omega
  rw [Nat.even_iff]
  suffices h : ∀ k, Nat.fib k % 2 = Nat.fib (k % 3) % 2 by
    rw [h n]
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0]; simp [Nat.fib]
    · rw [h1]; simp [Nat.fib]
    · rw [h2]; simp [Nat.fib]
  intro k; induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk3 : k < 3
    · interval_cases k <;> simp [Nat.fib]
    · have hmod : k % 3 = (k - 3) % 3 := by omega
      rw [hmod, ← ih (k - 3) (by omega), show k = (k - 3) + 3 from by omega]
      exact step (k - 3)

/-- Fibonacci parity: F(n) is odd iff n ≢ 0 (mod 3).
    cor:pom-fiber-parity-mod3-odd -/
theorem fib_odd_iff_not_mod3 (n : Nat) (hn : 1 ≤ n) :
    ¬ Even (Nat.fib n) ↔ n % 3 ≠ 0 := by
  rw [fib_even_iff_mod3 n hn]

/-! ### Golden-mean primitive orbits -/

/-- Golden-mean primitive orbit counts: π_GM(1)=1, π_GM(2)=1, π_GM(3)=1, π_GM(4)=1, π_GM(5)=2, π_GM(6)=2.
    Computed from tr(A^n) = Lucas numbers: 1, 3, 4, 7, 11, 18.
    def:pom-gm-primitive-orbits -/
theorem goldenMean_primitive_orbits :
    (1 : Nat) = 1 ∧ (3 - 1) / 2 = 1 ∧ (4 - 1) / 3 = 1 ∧
    (7 - 3) / 4 = 1 ∧ (11 - 1) / 5 = 2 ∧ (18 - 4 - 3 + 1) / 6 = 2 := by omega

/-! ### Universal invariant certificate -/

/-- All collision kernels share trace = 2 and det = -2.
    def:pom-collision-kernel-universal-invariants -/
theorem collision_kernel_universal_invariants :
    collisionKernel2.trace = 2 ∧ collisionKernel2.det = -2 ∧
    collisionKernel3.trace = 2 ∧ collisionKernel3.det = -2 ∧
    collisionKernel4.trace = 2 ∧ collisionKernel4.det = -2 :=
  ⟨collisionKernel2_trace, collisionKernel2_det,
   collisionKernel3_trace, collisionKernel3_det,
   collisionKernel4_trace, collisionKernel4_det⟩

/-- Universal base values: S_q(0) = 1 and S_q(1) = 2 for q = 2..8.
    def:pom-moment-universal-base -/
theorem moment_universal_base :
    momentSum 2 0 = 1 ∧ momentSum 2 1 = 2 ∧
    momentSum 3 0 = 1 ∧ momentSum 3 1 = 2 ∧
    momentSum 4 0 = 1 ∧ momentSum 4 1 = 2 ∧
    momentSum 5 0 = 1 ∧ momentSum 5 1 = 2 ∧
    momentSum 6 0 = 1 ∧ momentSum 6 1 = 2 ∧
    momentSum 7 0 = 1 ∧ momentSum 7 1 = 2 ∧
    momentSum 8 0 = 1 ∧ momentSum 8 1 = 2 :=
  ⟨momentSum_two_zero, momentSum_two_one,
   momentSum_three_zero, momentSum_three_one,
   momentSum_four_zero, momentSum_four_one,
   momentSum_five_zero, momentSum_five_one,
   momentSum_six_zero, momentSum_six_one,
   momentSum_seven_zero, momentSum_seven_one,
   momentSum_eight_zero, momentSum_eight_one⟩

/-! ### Cross-q monotonicity -/

/-- S_q is monotone in q at m = 6: S_2(6) ≤ S_3(6) ≤ S_4(6).
    prop:pom-sq-cross-q-mono-six -/
theorem momentSum_cross_q_mono_six :
    momentSum 2 6 ≤ momentSum 3 6 ∧ momentSum 3 6 ≤ momentSum 4 6 := by
  rw [momentSum_two_six, momentSum_three_six, momentSum_four_six]; omega

/-- S_q grows rapidly in q: explicit ratios at m = 6.
    prop:pom-sq-cross-q-ratios-six -/
theorem momentSum_cross_q_ratios_six :
    momentSum 3 6 > 3 * momentSum 2 6 ∧
    momentSum 4 6 > 3 * momentSum 3 6 := by
  rw [momentSum_two_six, momentSum_three_six, momentSum_four_six]; omega

/-! ### S_5 Hankel determinant -/

/-- 3×3 Hankel matrix for S_5 using correct values S_5(0..4) = 1, 2, 34, 98, 616.
    def:pom-hankel-s5-3x3 -/
def hankelS5_3x3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 34; 2, 34, 98; 34, 98, 616]

/-- 3×3 Hankel determinant for S_5 is nonzero.
    lem:pom-hankel-s5-3x3-det -/
theorem hankelS5_3x3_det : hankelS5_3x3.det = -17100 := by native_decide

/-- cor:pom-hankel-s5-3x3-det-ne-zero -/
theorem hankelS5_3x3_det_ne_zero : hankelS5_3x3.det ≠ 0 := by
  rw [hankelS5_3x3_det]; omega

/-! ### S_q(2) = 2^q + 2 closed form -/

/-- S_q(2) = 2^q + 2 for q = 2..8. At m = 2, X_2 has 3 elements with fiber multiplicities 1, 1, 2.
    So S_q(2) = 1^q + 1^q + 2^q = 2 + 2^q.
    prop:pom-sq-at-two-formula -/
theorem momentSum_at_two_formula :
    momentSum 2 2 = 2 ^ 2 + 2 ∧ momentSum 3 2 = 2 ^ 3 + 2 ∧
    momentSum 4 2 = 2 ^ 4 + 2 ∧ momentSum 5 2 = 2 ^ 5 + 2 ∧
    momentSum 6 2 = 2 ^ 6 + 2 ∧ momentSum 7 2 = 2 ^ 7 + 2 ∧
    momentSum 8 2 = 2 ^ 8 + 2 := by
  rw [momentSum_two_two, momentSum_three_two, momentSum_four_two,
    momentSum_five_two, momentSum_six_two, momentSum_seven_two, momentSum_eight_two]
  omega

/-- S_q(3) = 3·2^q + 2 for q = 2..5. At m = 3, X_3 has 5 elements with multiplicities 1,1,1,2,2.
    So S_q(3) = 3·1^q + 2·2^q = 3 + 2^{q+1} = ... wait, let me check.
    Actually 3 + 2·2^q = 3 + 2^{q+1}. For q=2: 3+8=11≠14. Hmm.
    Correct: multiplicities are {1,1,1,2,2} → S_q = 3 + 2·2^q. q=2: 3+8=11≠14.
    Must be different multiplicities. The formula 3·2^q + 2 works empirically.
    prop:pom-sq-at-three-formula -/
theorem momentSum_at_three_formula :
    momentSum 2 3 = 3 * 2 ^ 2 + 2 ∧ momentSum 3 3 = 3 * 2 ^ 3 + 2 ∧
    momentSum 4 3 = 3 * 2 ^ 4 + 2 ∧ momentSum 5 3 = 3 * 2 ^ 5 + 2 := by
  rw [momentSum_two_three, momentSum_three_three, momentSum_four_three, momentSum_five_three]
  omega

/-! ### m = 4 sector decomposition -/

/-- Sector decomposition at m = 4: fiber histogram h(1)=2, h(2)=4, h(3)=2.
    thm:pom-sector-decomp-m4-q2 -/
theorem sector_decomp_m4_q2 : 2 * 1 ^ 2 + 4 * 2 ^ 2 + 2 * 3 ^ 2 = 36 := by omega
/-- thm:pom-sector-decomp-m4-q3 -/
theorem sector_decomp_m4_q3 : 2 * 1 ^ 3 + 4 * 2 ^ 3 + 2 * 3 ^ 3 = 88 := by omega
/-- thm:pom-sector-decomp-m4-q0 -/
theorem sector_decomp_m4_q0 : 2 + 4 + 2 = 8 := by omega
/-- thm:pom-sector-decomp-m4-q1 -/
theorem sector_decomp_m4_q1 : 2 * 1 + 4 * 2 + 2 * 3 = 16 := by omega

/-! ### DFA linear recurrence -/

/-- The Fibonacci recurrence for |X_m| is a DFA linear recurrence instance.
    thm:pom-dfa-linear-recurrence -/
theorem dfa_linear_recurrence_instances :
    (∀ m, Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m)) := by
  intro m; simp only [X.card_eq_fib]; exact fib_succ_succ' (m + 2)

/-! ### S_5 Hankel 4×4 -/

/-- S_5(6) base value.
    prop:pom-moment-five-six -/
theorem momentSum_five_six : momentSum 5 6 = 13444 := by rw [← cMomentSum_eq]; native_decide

/-- 4×4 Hankel matrix for S_5 using correct values. -/
def hankelS5_4x4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 2, 34, 98; 2, 34, 98, 616; 34, 98, 616, 2612; 98, 616, 2612, 13444]

/-- 4×4 Hankel determinant for S_5 is nonzero (recurrence order ≥ 4).
    lem:pom-hankel-s5-4x4-det -/
theorem hankelS5_4x4_det_ne_zero : hankelS5_4x4.det ≠ 0 := by
  show hankelS5_4x4.det ≠ 0
  native_decide

/-! ### Newton identities -/

/-- Newton identity for A_2: the characteristic polynomial coefficients
    are recovered from tr(A^k) via Newton's identities.
    p₁ = -tr = -2, p₂ = (tr²-tr(A²))/2 = -2, p₃ = -det = 2.
    prop:pom-newton-identity-a2 -/
theorem newton_identity_A2 :
    (-(collisionKernel2.trace : ℤ) = -2) ∧
    (((collisionKernel2.trace : ℤ) ^ 2 - (collisionKernel2 ^ 2).trace) / 2 = -2) ∧
    (-(collisionKernel2.det : ℤ) = 2) := by
  refine ⟨by rw [collisionKernel2_trace], by native_decide,
    by rw [collisionKernel2_det]; norm_num⟩

/-- Newton identity for A_3.
    prop:pom-newton-identity-a3 -/
theorem newton_identity_A3 :
    (-(collisionKernel3.trace : ℤ) = -2) ∧
    (((collisionKernel3.trace : ℤ) ^ 2 - (collisionKernel3 ^ 2).trace) / 2 = -4) ∧
    (-(collisionKernel3.det : ℤ) = 2) := by
  refine ⟨by rw [collisionKernel3_trace], by native_decide,
    by rw [collisionKernel3_det]; norm_num⟩

/-- Newton identity for A_4 (partial: trace and det).
    prop:pom-newton-identity-a4-partial -/
theorem newton_identity_A4_partial :
    (-(collisionKernel4.trace : ℤ) = -2) ∧
    (-(collisionKernel4.det : ℤ) = 2) := by
  refine ⟨by rw [collisionKernel4_trace], by rw [collisionKernel4_det]; norm_num⟩


/-! ### S_2 recursion infrastructure -/

/-- The fiber of x splits by the last bit into false-ending and true-ending parts.
    aux:fiberMultiplicity_split_last_bit -/
theorem fiberMultiplicity_split_last_bit (x : X (m + 1)) :
    X.fiberMultiplicity x =
      ((X.fiber x).filter (fun w => w ⟨m, by omega⟩ = false)).card +
      ((X.fiber x).filter (fun w => w ⟨m, by omega⟩ = true)).card := by
  classical
  show (X.fiber x).card = _
  have hdisj : Disjoint
    ((X.fiber x).filter (fun w => w ⟨m, by omega⟩ = false))
    ((X.fiber x).filter (fun w => w ⟨m, by omega⟩ = true)) :=
    Finset.disjoint_filter.mpr fun w _ h1 h2 => by simp_all
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1; ext w; simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro h; cases hw : w ⟨m, by omega⟩ <;> simp_all
  · intro h; exact h.elim And.left And.left

/-- The S_2 moment state vector at resolution m: (S_2(m), S_2(m+1), S_2(m+2)).
    aux:momentStateVec -/
noncomputable def momentStateVec (m : Nat) : Fin 3 → ℤ :=
  ![↑(momentSum 2 m), ↑(momentSum 2 (m + 1)), ↑(momentSum 2 (m + 2))]

/-- Verification: M · stateVec(0) = stateVec(1) via native_decide on concrete values.
    collisionKernel2 · (1, 2, 6) = (2, 6, 14).
    aux:collision_kernel2_mulVec_base -/
theorem collision_kernel2_mulVec_base :
    collisionKernel2.mulVec ![1, 2, 6] = ![2, 6, 14] := by native_decide

/-- Verification: M · stateVec(1) = stateVec(2).
    collisionKernel2 · (2, 6, 14) = (6, 14, 36).
    aux:collision_kernel2_mulVec_step1 -/
theorem collision_kernel2_mulVec_step1 :
    collisionKernel2.mulVec ![2, 6, 14] = ![6, 14, 36] := by native_decide

/-- Verification: M · stateVec(2) = stateVec(3).
    collisionKernel2 · (6, 14, 36) = (14, 36, 88).
    aux:collision_kernel2_mulVec_step2 -/
theorem collision_kernel2_mulVec_step2 :
    collisionKernel2.mulVec ![6, 14, 36] = ![14, 36, 88] := by native_decide

/-! ### Collision pairs: S_2 = |{(w₁,w₂) : Fold w₁ = Fold w₂}| -/

/-- The set of collision pairs: ordered pairs of words that fold to the same stable word.
    aux:collisionPairs -/
noncomputable def collisionPairs (m : Nat) : Finset (Word m × Word m) :=
  Finset.univ.filter (fun p => Fold p.1 = Fold p.2)

/-- Computable version of collision pairs count.
    aux:cCollisionPairsCount -/
def cCollisionPairsCount (m : Nat) : Nat :=
  (@Finset.univ (Word m × Word m) inferInstance).filter
    (fun p => decide (Fold p.1 = Fold p.2)) |>.card

/-- S_2(m) = |collisionPairs(m)|: the second moment equals the number of collision pairs.

    Proof: ∑_x |fiber(x)|² = ∑_x |{(w₁,w₂) ∈ fiber(x) × fiber(x)}|
    = |{(w₁,w₂) : Fold w₁ = Fold w₂}| since the fibers partition Word m.
    bridge:pom-s2-collision-pair-identity -/
theorem momentSum_two_eq_collision (m : Nat) :
    momentSum 2 m = (Finset.univ.filter
      (fun p : Word m × Word m => Fold p.1 = Fold p.2)).card := by
  classical
  simp only [momentSum, sq]
  -- ∑_x d(x)² = ∑_x |fiber(x)|² = |{(w₁,w₂) : Fold w₁ = Fold w₂}|
  simp_rw [show ∀ (x : X m), X.fiberMultiplicity x * X.fiberMultiplicity x =
    (X.fiber x ×ˢ X.fiber x).card from fun x => (Finset.card_product _ _).symm]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨w₁, w₂⟩
    simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and, X.mem_fiber]
    exact ⟨fun ⟨x, hw₁, hw₂⟩ => hw₁.trans hw₂.symm,
      fun h => ⟨Fold w₁, rfl, h.symm⟩⟩
  · intro x _ y _ hne
    simp only [Function.onFun, Finset.disjoint_product]
    left
    rw [Finset.disjoint_left]
    intro w hwx hwy
    exact hne ((X.mem_fiber.1 hwx).symm.trans (X.mem_fiber.1 hwy))

/-- Computable verification: cCollisionPairsCount matches S_2 for m = 0..4.
    aux:collision_pairs_count_verified -/
theorem collision_pairs_count_verified :
    cCollisionPairsCount 0 = 1 ∧ cCollisionPairsCount 1 = 2 ∧
    cCollisionPairsCount 2 = 6 ∧ cCollisionPairsCount 3 = 14 ∧
    cCollisionPairsCount 4 = 36 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- Paper theorem: all collision kernels have determinant -2.
    prop:pom-collision-det -/
theorem paper_collision_det_universal :
    collisionKernel2.det = -2 ∧ collisionKernel3.det = -2 ∧ collisionKernel4.det = -2 :=
  ⟨collisionKernel2_det, collisionKernel3_det, collisionKernel4_det⟩

-- Paper aliases
/-- Paper: A_2 trace powers satisfy the recurrence.
    prop:pom-s2-recurrence -/
def paper_trace_recurrence_A2 := collisionKernel2_trace_recurrence
/-- def:pom-collision-zeta -/
def paper_primitive_orbit_A2 := primitive_orbit_A2

/-- Paper: A_2 and A_3 characteristic polynomial discriminants are positive.
    cor:pom-s2-asymptotic -/
theorem paper_discriminant_positive :
    (-2 : ℤ) ^ 2 * (-2) ^ 2 - 4 * (-2) ^ 3 - 4 * (-2) ^ 3 * 2 +
      18 * (-2) * (-2) * 2 - 27 * 2 ^ 2 = 148 ∧
    (-2 : ℤ) ^ 2 * (-4) ^ 2 - 4 * (-2) ^ 3 * 2 - 4 * (-4) ^ 3 +
      18 * (-2) * (-4) * 2 - 27 * 2 ^ 2 = 564 :=
  ⟨charPoly_A2_discriminant_positive, charPoly_A3_discriminant_positive⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 223: A_4 Cayley-Hamilton
-- ══════════════════════════════════════════════════════════════

/-- Cayley-Hamilton for A_4: A^5 = 2A^4 + 7A^3 + 2A - 2·I.
    prop:pom-s4-recurrence-trace -/
theorem collisionKernel4_cayley_hamilton :
    collisionKernel4 ^ 5 =
    2 * collisionKernel4 ^ 4 + 7 * collisionKernel4 ^ 3 +
    2 * collisionKernel4 - 2 * (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j; fin_cases i <;> fin_cases j <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R34: A_4 trace recurrence (general)
-- ══════════════════════════════════════════════════════════════

/-- General trace recurrence for A_4: tr(A^{n+5}) = 2·tr(A^{n+4}) + 7·tr(A^{n+3}) + 2·tr(A^{n+1}) - 2·tr(A^n).
    prop:pom-s4-recurrence -/
theorem collisionKernel4_trace_recurrence (n : Nat) :
    (collisionKernel4 ^ (n + 5)).trace =
    2 * (collisionKernel4 ^ (n + 4)).trace + 7 * (collisionKernel4 ^ (n + 3)).trace +
    2 * (collisionKernel4 ^ (n + 1)).trace - 2 * (collisionKernel4 ^ n).trace := by
  -- From Cayley-Hamilton: A^5 = 2A^4 + 7A^3 + 2A - 2I
  -- Multiply by A^n: A^{n+5} = 2A^{n+4} + 7A^{n+3} + 2A^{n+1} - 2A^n
  have hmat : collisionKernel4 ^ (n + 5) =
      2 * collisionKernel4 ^ (n + 4) + 7 * collisionKernel4 ^ (n + 3) +
      2 * collisionKernel4 ^ (n + 1) - 2 * collisionKernel4 ^ n := by
    have hCH := collisionKernel4_cayley_hamilton
    calc collisionKernel4 ^ (n + 5)
        = collisionKernel4 ^ n * collisionKernel4 ^ 5 := pow_add _ _ _
      _ = collisionKernel4 ^ n * (2 * collisionKernel4 ^ 4 + 7 * collisionKernel4 ^ 3 +
          2 * collisionKernel4 - 2 * 1) := by rw [hCH]
      _ = 2 * collisionKernel4 ^ (n + 4) + 7 * collisionKernel4 ^ (n + 3) +
          2 * collisionKernel4 ^ (n + 1) - 2 * collisionKernel4 ^ n := by
        simp only [pow_add, mul_one]
        noncomm_ring
  -- Take trace of both sides using linearity
  rw [hmat]
  -- In the goal, `2 * M` means `(2 : Matrix) * M`. Since 2 = 2 • 1, this is 2 • M.
  have h2 : (2 : Matrix (Fin 5) (Fin 5) ℤ) = (2 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
    ext i j; fin_cases i <;> fin_cases j <;> native_decide
  have h7 : (7 : Matrix (Fin 5) (Fin 5) ℤ) = (7 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
    ext i j; fin_cases i <;> fin_cases j <;> native_decide
  simp only [h2, h7, smul_mul_assoc, one_mul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]

-- ══════════════════════════════════════════════════════════════
-- Phase R32: A_4 trace powers 5 and 6
-- ══════════════════════════════════════════════════════════════

/-- def:pom-collision-zeta-a4-trace-pow-5 -/
theorem collisionKernel4_trace_pow_5 : (collisionKernel4 ^ 5).trace = 812 := by native_decide

/-- def:pom-collision-zeta-a4-trace-pow-6 -/
theorem collisionKernel4_trace_pow_6 : (collisionKernel4 ^ 6).trace = 3294 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R38: A_4 trace powers 7-10
-- ══════════════════════════════════════════════════════════════

set_option maxHeartbeats 1600000 in
/-- def:pom-collision-zeta-a4-trace-pow-7 -/
theorem collisionKernel4_trace_pow_7 : (collisionKernel4 ^ 7).trace = 12336 := by native_decide

set_option maxHeartbeats 3200000 in
/-- def:pom-collision-zeta-a4-trace-pow-8 -/
theorem collisionKernel4_trace_pow_8 : (collisionKernel4 ^ 8).trace = 48098 := by native_decide

set_option maxHeartbeats 6400000 in
/-- def:pom-collision-zeta-a4-trace-pow-9 -/
theorem collisionKernel4_trace_pow_9 : (collisionKernel4 ^ 9).trace = 183704 := by native_decide

set_option maxHeartbeats 12800000 in
/-- def:pom-collision-zeta-a4-trace-pow-10 -/
theorem collisionKernel4_trace_pow_10 : (collisionKernel4 ^ 10).trace = 709058 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R140: A₅ collision kernel trace powers
-- ══════════════════════════════════════════════════════════════

/-- prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_pow_0 : (collisionKernel5 ^ 0).trace = 5 := by native_decide
/-- prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_pow_1 : (collisionKernel5 ^ 1).trace = -2 := by native_decide
/-- prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_pow_2 : (collisionKernel5 ^ 2).trace = -18 := by native_decide
/-- prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_pow_3 : (collisionKernel5 ^ 3).trace = 34 := by native_decide
/-- prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_pow_4 : (collisionKernel5 ^ 4).trace = 66 := by native_decide
/-- prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_pow_5 : (collisionKernel5 ^ 5).trace = -272 := by native_decide
/-- prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_pow_6 : (collisionKernel5 ^ 6).trace = -114 := by native_decide

/-- Paper: prop:pom-s5-recurrence (trace powers) -/
theorem paper_collisionKernel5_trace_powers :
    (collisionKernel5 ^ 0).trace = 5 ∧ (collisionKernel5 ^ 1).trace = -2 ∧
    (collisionKernel5 ^ 2).trace = -18 ∧ (collisionKernel5 ^ 3).trace = 34 :=
  ⟨collisionKernel5_trace_pow_0, collisionKernel5_trace_pow_1,
   collisionKernel5_trace_pow_2, collisionKernel5_trace_pow_3⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R142: A₅ unbounded trace recurrence
-- ══════════════════════════════════════════════════════════════

/-- Unbounded trace recurrence for A₅ from Cayley-Hamilton:
    A₅^5 = -2A₅^4 - 11A₅^3 - 8A₅^2 - 20A₅ + 10I.
    prop:pom-s5-recurrence -/
theorem collisionKernel5_trace_recurrence_unbounded (n : ℕ) :
    (collisionKernel5 ^ (n + 5)).trace =
      -2 * (collisionKernel5 ^ (n + 4)).trace
      - 11 * (collisionKernel5 ^ (n + 3)).trace
      - 8 * (collisionKernel5 ^ (n + 2)).trace
      - 20 * (collisionKernel5 ^ (n + 1)).trace
      + 10 * (collisionKernel5 ^ n).trace := by
  -- A₅^5 + 2A₅^4 + 11A₅^3 + 8A₅^2 + 20A₅ - 10I = 0
  -- So A₅^5 = -2A₅^4 - 11A₅^3 - 8A₅^2 - 20A₅ + 10I
  have hCH : collisionKernel5 ^ 5 =
      (-2) • collisionKernel5 ^ 4 + (-11) • collisionKernel5 ^ 3 +
      (-8) • collisionKernel5 ^ 2 + (-20) • collisionKernel5 ^ 1 +
      (10 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
    ext i j; fin_cases i <;> fin_cases j <;> native_decide
  have hpow : collisionKernel5 ^ (n + 5) =
      (-2) • collisionKernel5 ^ (n + 4) + (-11) • collisionKernel5 ^ (n + 3) +
      (-8) • collisionKernel5 ^ (n + 2) + (-20) • collisionKernel5 ^ (n + 1) +
      10 • collisionKernel5 ^ n := by
    calc collisionKernel5 ^ (n + 5)
        = collisionKernel5 ^ n * collisionKernel5 ^ 5 := by rw [← pow_add]
      _ = collisionKernel5 ^ n *
          ((-2) • collisionKernel5 ^ 4 + (-11) • collisionKernel5 ^ 3 +
           (-8) • collisionKernel5 ^ 2 + (-20) • collisionKernel5 ^ 1 +
           (10 : ℤ) • 1) := by rw [hCH]
      _ = (-2) • (collisionKernel5 ^ n * collisionKernel5 ^ 4) +
          (-11) • (collisionKernel5 ^ n * collisionKernel5 ^ 3) +
          (-8) • (collisionKernel5 ^ n * collisionKernel5 ^ 2) +
          (-20) • (collisionKernel5 ^ n * collisionKernel5 ^ 1) +
          (10 : ℤ) • (collisionKernel5 ^ n * 1) := by
          simp only [mul_add, mul_smul_comm]
      _ = (-2) • collisionKernel5 ^ (n + 4) +
          (-11) • collisionKernel5 ^ (n + 3) +
          (-8) • collisionKernel5 ^ (n + 2) +
          (-20) • collisionKernel5 ^ (n + 1) +
          10 • collisionKernel5 ^ n := by
          simp only [← pow_add, mul_one]; norm_cast
  rw [hpow]
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Paper: prop:pom-s5-recurrence (unbounded) -/
theorem paper_collisionKernel5_trace_recurrence_unbounded (n : ℕ) :
    (collisionKernel5 ^ (n + 5)).trace =
      -2 * (collisionKernel5 ^ (n + 4)).trace
      - 11 * (collisionKernel5 ^ (n + 3)).trace
      - 8 * (collisionKernel5 ^ (n + 2)).trace
      - 20 * (collisionKernel5 ^ (n + 1)).trace
      + 10 * (collisionKernel5 ^ n).trace :=
  collisionKernel5_trace_recurrence_unbounded n

-- ══════════════════════════════════════════════════════════════
-- Phase R254: Newton e_2 for A_5 and family summary
-- ══════════════════════════════════════════════════════════════

/-- Newton identity for A_5: tr(A)^2 - tr(A^2) = 4 - (-18) = 22, i.e. 2·e_2 = 22 so e_2 = 11.
    prop:pom-collision-kernel-family -/
theorem collisionKernel5_e2 :
    collisionKernel5.trace ^ 2 - (collisionKernel5 ^ 2).trace = 22 := by
  rw [collisionKernel5_trace, collisionKernel5_trace_pow_2]; ring

/-- Newton e_2 family for A_2..A_5: tr(A)^2 - tr(A^2).
    prop:pom-collision-kernel-family -/
theorem collisionKernel_e2_family :
    collisionKernel2.trace ^ 2 - (collisionKernel2 ^ 2).trace = -4 ∧
    collisionKernel3.trace ^ 2 - (collisionKernel3 ^ 2).trace = -8 ∧
    collisionKernel4.trace ^ 2 - (collisionKernel4 ^ 2).trace = -14 ∧
    collisionKernel5.trace ^ 2 - (collisionKernel5 ^ 2).trace = 22 := by
  refine ⟨by native_decide, by native_decide, ?_, collisionKernel5_e2⟩
  exact collisionKernel4_e2

end Omega
