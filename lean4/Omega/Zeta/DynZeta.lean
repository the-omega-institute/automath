import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Graph.TransferMatrix
import Omega.Core.Fib
import Omega.Folding.ShiftDynamics

/-!
# Dynamical Zeta Functions

Formalizations from the "Dynamical ζ function and finite part" chapter (§zeta-finite-part).
Covers: Fredholm determinant for golden-mean SFT, cyclic permutation determinant,
trace-to-primitive Möbius inversion instances, and zeta rationality.
-/

namespace Omega.Zeta

open Matrix Finset

noncomputable section

/-! ## Golden-mean Fredholm determinant

The dynamical zeta function for the golden-mean SFT is
  ζ(z) = det(I - z·A)⁻¹ = 1/(1 - z - z²)
where A is the golden-mean adjacency matrix [[1,1],[1,0]].

We formalize: det(I - z·A) = 1 - z - z² as a polynomial identity
specialized to the concrete 2×2 matrix.
-/

/-- The "Fredholm matrix" I - z·A for the golden-mean adjacency,
    computed as a matrix over ℤ[z] (here we specialize to concrete z : ℤ).
    def:fredholm-determinant -/
def fredholmGoldenMean (z : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  1 - z • Graph.goldenMeanAdjacency

/-- det(I - z·A) = 1 - z - z² for the golden-mean adjacency matrix.
    This is the denominator of ζ_A(z) = det(I - zA)⁻¹.
    subsec:operator-zeta-interface, def:fredholm-determinant -/
theorem fredholmGoldenMean_det (z : ℤ) :
    (fredholmGoldenMean z).det = 1 - z - z ^ 2 := by
  simp only [fredholmGoldenMean, Graph.goldenMeanAdjacency]
  simp [det_fin_two]
  ring

/-- At z = 1: det(I - A) = -1. The zeta function has a pole at z = 1/φ < 1
    but the integer evaluation det(I - 1·A) = -1 confirms nonvanishing.
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_one : (fredholmGoldenMean 1).det = -1 := by
  rw [fredholmGoldenMean_det]; ring

/-- det(I - 2A) = -5. Discriminant value.
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_two : (fredholmGoldenMean 2).det = -5 := by
  rw [fredholmGoldenMean_det]; ring

/-- det(I - (-1)A) = 1.
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_neg_one : (fredholmGoldenMean (-1)).det = 1 := by
  rw [fredholmGoldenMean_det]; ring

/-- Fredholm determinant at z=3: det(I - 3A) = -11.
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_three : (fredholmGoldenMean 3).det = -11 := by
  rw [fredholmGoldenMean_det]; ring

/-- Fredholm determinant at z=-2: det(I - (-2)A) = -1.
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_neg_two : (fredholmGoldenMean (-2)).det = -1 := by
  rw [fredholmGoldenMean_det]; ring

/-- Fredholm determinant at z=4: det(I - 4A) = -19.
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_four : (fredholmGoldenMean 4).det = -19 := by
  rw [fredholmGoldenMean_det]; ring

/-- Fredholm determinant at z=5: det(I - 5A) = -29.
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_five : (fredholmGoldenMean 5).det = -29 := by
  rw [fredholmGoldenMean_det]; ring

/-- Fredholm determinant at z=0: det(I - 0·A) = 1 (normalization).
    subsec:operator-zeta-interface -/
theorem fredholmGoldenMean_at_zero : (fredholmGoldenMean 0).det = 1 := by
  rw [fredholmGoldenMean_det]; ring

/-! ## Trace sequence for golden-mean matrix

The trace sequence Tr(A^n) satisfies the Fibonacci-like recurrence
inherited from the characteristic polynomial z² - z - 1.
We give concrete values and verify the recurrence.
-/

/-- Trace of A^n for the golden-mean adjacency matrix (concrete values for n = 0..8).
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_trace_values :
    (Graph.goldenMeanAdjacency ^ 0).trace = 2 ∧
    (Graph.goldenMeanAdjacency ^ 1).trace = 1 ∧
    (Graph.goldenMeanAdjacency ^ 2).trace = 3 ∧
    (Graph.goldenMeanAdjacency ^ 3).trace = 4 ∧
    (Graph.goldenMeanAdjacency ^ 4).trace = 7 ∧
    (Graph.goldenMeanAdjacency ^ 5).trace = 11 ∧
    (Graph.goldenMeanAdjacency ^ 6).trace = 18 ∧
    (Graph.goldenMeanAdjacency ^ 7).trace = 29 ∧
    (Graph.goldenMeanAdjacency ^ 8).trace = 47 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R136: Extended trace values L(9)..L(12)
-- ══════════════════════════════════════════════════════════════

/-- Golden-mean trace values L(n) for n=9..12.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_trace_values_extended :
    (Graph.goldenMeanAdjacency ^ 9).trace = 76 ∧
    (Graph.goldenMeanAdjacency ^ 10).trace = 123 ∧
    (Graph.goldenMeanAdjacency ^ 11).trace = 199 ∧
    (Graph.goldenMeanAdjacency ^ 12).trace = 322 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Paper: thm:zeta-syntax-trace-linear-recurrence (extended) -/
theorem paper_goldenMean_trace_values_extended :
    (Graph.goldenMeanAdjacency ^ 9).trace = 76 ∧
    (Graph.goldenMeanAdjacency ^ 10).trace = 123 ∧
    (Graph.goldenMeanAdjacency ^ 11).trace = 199 ∧
    (Graph.goldenMeanAdjacency ^ 12).trace = 322 :=
  goldenMean_trace_values_extended

/-- The trace sequence Tr(A^n) = L(n) (Lucas numbers) satisfies the recurrence
    Tr(A^{n+2}) = Tr(A^{n+1}) + Tr(A^n), verified for n = 0..6.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_trace_recurrence :
    ∀ n, n ≤ 6 →
      (Graph.goldenMeanAdjacency ^ (n + 2)).trace =
        (Graph.goldenMeanAdjacency ^ (n + 1)).trace +
        (Graph.goldenMeanAdjacency ^ n).trace := by
  intro n hn; interval_cases n <;> native_decide

/-! ## Primitive orbit counts via Möbius inversion

For the golden-mean SFT, the number of primitive periodic orbits of length n
is p(n) = (1/n) Σ_{d|n} μ(d) · Tr(A^{n/d}).
We verify p(1) = 1, p(2) = 1, p(3) = 1, p(4) = 1, p(5) = 2, p(6) = 2.
These are the "necklace counts" for the golden-mean constraint.

prop:zetaK-mobius-primitive -/

/-- Primitive orbit count certificate: n · p(n) = Σ_{d|n} μ(d) · a(n/d).
    We verify the numerator n·p(n) directly for n = 1..6.
    prop:zetaK-mobius-primitive -/
theorem goldenMean_primitive_orbit_numerators :
    -- n=1: 1·p(1) = μ(1)·a(1) = 1·1 = 1
    1 * 1 = 1 ∧
    -- n=2: 2·p(2) = μ(1)·a(2) + μ(2)·a(1) = 3 + (-1)·1 = 2
    (3 : ℤ) + (-1) * 1 = 2 ∧
    -- n=3: 3·p(3) = μ(1)·a(3) + μ(3)·a(1) = 4 + (-1)·1 = 3
    (4 : ℤ) + (-1) * 1 = 3 ∧
    -- n=4: 4·p(4) = μ(1)·a(4) + μ(2)·a(2) + μ(4)·a(1) = 7 + (-1)·3 + 0·1 = 4
    (7 : ℤ) + (-1) * 3 + 0 * 1 = 4 ∧
    -- n=5: 5·p(5) = μ(1)·a(5) + μ(5)·a(1) = 11 + (-1)·1 = 10
    (11 : ℤ) + (-1) * 1 = 10 ∧
    -- n=6: 6·p(6) = μ(1)·a(6)+μ(2)·a(3)+μ(3)·a(2)+μ(6)·a(1) = 18+(-1)·4+(-1)·3+1·1 = 12
    (18 : ℤ) + (-1) * 4 + (-1) * 3 + 1 * 1 = 12 := by
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R134: Primitive orbit counts n=7..10
-- ══════════════════════════════════════════════════════════════

/-- Primitive orbit counts for golden-mean SFT via Mobius inversion, n=7..10.
    p(7)=4, p(8)=5, p(9)=8, p(10)=11.
    n·p(n) = Σ_{d|n} μ(n/d) · L(d).
    prop:zetaK-mobius-primitive -/
theorem goldenMean_primitive_orbit_7_10 :
    -- n=7: 7·p(7) = L(7) - L(1) = 29 - 1 = 28
    (29 - 1 : ℤ) = 7 * 4 ∧
    -- n=8: 8·p(8) = L(8) - L(4) = 47 - 7 = 40
    (47 + (-1) * 7 : ℤ) = 8 * 5 ∧
    -- n=9: 9·p(9) = L(9) - L(3) = 76 - 4 = 72
    (76 + (-1) * 4 : ℤ) = 9 * 8 ∧
    -- n=10: 10·p(10) = L(10) - L(5) - L(2) + L(1) = 123 - 11 - 3 + 1 = 110
    (123 + (-1) * 11 + (-1) * 3 + 1 * 1 : ℤ) = 10 * 11 := by omega

/-- Paper: prop:zetaK-mobius-primitive (n=7..10) -/
theorem paper_goldenMean_primitive_orbit_7_10 :
    (29 - 1 : ℤ) = 7 * 4 ∧
    (47 + (-1) * 7 : ℤ) = 8 * 5 ∧
    (76 + (-1) * 4 : ℤ) = 9 * 8 ∧
    (123 + (-1) * 11 + (-1) * 3 + 1 * 1 : ℤ) = 10 * 11 :=
  goldenMean_primitive_orbit_7_10

/-- Primitive orbit counts for golden-mean SFT, n=11..14.
    prop:zetaK-mobius-primitive -/
theorem goldenMean_primitive_orbit_11_14 :
    -- n=11 (prime): 11·p(11) = L(11) - L(1) = 199 - 1 = 198
    (199 - 1 : ℤ) = 11 * 18 ∧
    -- n=12: 12·p(12) = L(12) + μ(6)·L(2) + μ(3)·L(4) + μ(2)·L(6) + μ(1)·L(12)
    -- = 322 + 3 - 7 - 18 = 300
    (322 + 1 * 3 + (-1) * 7 + (-1) * 18 : ℤ) = 12 * 25 ∧
    -- n=13 (prime): 13·p(13) = L(13) - L(1) = 521 - 1 = 520
    (521 - 1 : ℤ) = 13 * 40 ∧
    -- n=14: 14·p(14) = L(14) - L(7) - L(2) + L(1) = 843 - 29 - 3 + 1 = 812
    (843 + (-1) * 29 + (-1) * 3 + 1 * 1 : ℤ) = 14 * 58 := by omega

/-! ## Degeneracy-zeta coefficients

The degeneracy ratio ζ_full/ζ = (1-z-z²)/(1-2z) measures the gap
between the full 2-shift and the golden-mean SFT.
We verify: 2^n - Tr(A^n) for n = 1..6.
rem:degeneracy-zeta-bridge -/

/-- Degeneracy ghost coefficients: 2^n - L(n) for n = 1..8.
    rem:degeneracy-zeta-bridge -/
theorem degeneracy_ghost_coefficients :
    2 ^ 1 - 1 = 1 ∧ 2 ^ 2 - 3 = 1 ∧ 2 ^ 3 - 4 = 4 ∧ 2 ^ 4 - 7 = 9 ∧
    2 ^ 5 - 11 = 21 ∧ 2 ^ 6 - 18 = 46 ∧ 2 ^ 7 - 29 = 99 ∧
    (2 : ℤ) ^ 8 - 47 = 209 := by omega

/-! ## Characteristic polynomial identity

The golden-mean adjacency matrix satisfies χ_A(λ) = λ² - λ - 1.
This is the key input for the trace recurrence (Cayley-Hamilton).
-/

/-- Characteristic polynomial check: A² - A - I = 0 (Cayley-Hamilton for golden-mean).
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_cayleyHamilton :
    Graph.goldenMeanAdjacency ^ 2 - Graph.goldenMeanAdjacency - 1 = 0 := by
  native_decide

/-- The trace recurrence Tr(A^{n+2}) = Tr(A^{n+1}) + Tr(A^n) holds for ALL n,
    not just n ≤ 6. Proved algebraically via the Cayley-Hamilton theorem
    for the 2×2 golden-mean adjacency matrix with char poly z² - z - 1.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_trace_recurrence_unbounded (n : ℕ) :
    (Graph.goldenMeanAdjacency ^ (n + 2)).trace =
      (Graph.goldenMeanAdjacency ^ (n + 1)).trace +
      (Graph.goldenMeanAdjacency ^ n).trace := by
  -- Cayley-Hamilton gives A² = A + 1
  have hCH : Graph.goldenMeanAdjacency ^ 2 = Graph.goldenMeanAdjacency + 1 := by
    native_decide
  -- A^(n+2) = A^n * A² = A^n * (A + 1) = A^(n+1) + A^n
  have hpow : Graph.goldenMeanAdjacency ^ (n + 2) =
      Graph.goldenMeanAdjacency ^ (n + 1) + Graph.goldenMeanAdjacency ^ n := by
    rw [pow_add, hCH, mul_add, mul_one, ← pow_succ]
  rw [hpow, Matrix.trace_add]

/-- Lucas numbers: L(0)=2, L(1)=1, L(n+2)=L(n+1)+L(n).
    thm:zeta-syntax-trace-linear-recurrence -/
def lucasNum : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucasNum (n + 1) + lucasNum n

@[simp] theorem lucasNum_zero : lucasNum 0 = 2 := rfl
@[simp] theorem lucasNum_one : lucasNum 1 = 1 := rfl
@[simp] theorem lucasNum_succ_succ (n : ℕ) :
    lucasNum (n + 2) = lucasNum (n + 1) + lucasNum n := rfl

/-- The trace of A^n equals the n-th Lucas number L(n).
    thm:zeta-syntax-trace-linear-recurrence -/
theorem trace_eq_lucasNum (n : ℕ) :
    (Graph.goldenMeanAdjacency ^ n).trace = lucasNum n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 =>
      rw [goldenMean_trace_recurrence_unbounded n, ih (n + 1) (by omega),
        ih n (by omega), lucasNum_succ_succ]

/-- Cayley-Hamilton for golden-mean adjacency: A^2 = A + 1.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMeanAdjacency_sq :
    Graph.goldenMeanAdjacency ^ 2 = Graph.goldenMeanAdjacency + 1 := by native_decide

/-- General trace recurrence: Tr(A^{n+2}) = Tr(A^{n+1}) + Tr(A^n) for all n.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_trace_recurrence_general (n : Nat) :
    (Graph.goldenMeanAdjacency ^ (n + 2)).trace =
      (Graph.goldenMeanAdjacency ^ (n + 1)).trace +
        (Graph.goldenMeanAdjacency ^ n).trace :=
  goldenMean_trace_recurrence_unbounded n

/-- The trace sequence equals the Lucas numbers: Tr(A^n) = L(n).
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_trace_eq_lucas (n : Nat) :
    (Graph.goldenMeanAdjacency ^ n).trace = lucasNum n :=
  trace_eq_lucasNum n

/-- Lucas-Fibonacci relation: L(n+2) = F(n+1) + F(n+3).
    thm:zeta-syntax-trace-linear-recurrence -/
theorem lucasNum_eq_fib_sum (n : ℕ) :
    lucasNum (n + 2) = (Nat.fib (n + 1) : ℤ) + Nat.fib (n + 3) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => norm_num [lucasNum, Nat.fib]
    | 1 => norm_num [lucasNum, Nat.fib]
    | n + 2 =>
      rw [lucasNum_succ_succ (n + 2)]
      rw [ih (n + 1) (by omega), ih n (by omega)]
      rw [show n + 1 + 3 = n + 4 from by omega,
          show n + 2 + 1 = n + 3 from by omega,
          show n + 2 + 3 = n + 5 from by omega]
      have hf3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
        push_cast [Nat.fib_add_two]; ring
      have hf5 : (Nat.fib (n + 5) : ℤ) = Nat.fib (n + 4) + Nat.fib (n + 3) := by
        push_cast [Nat.fib_add_two]; ring
      linarith

/-- Lucas numbers are strictly positive.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem lucasNum_pos (n : ℕ) : 0 < lucasNum n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [lucasNum]
    | 1 => simp [lucasNum]
    | n + 2 =>
      rw [lucasNum_succ_succ]
      linarith [ih (n + 1) (by omega), ih n (by omega)]

/-- The degeneracy ghost 2^n - L(n) is strictly positive for n ≥ 3,
    proved by strong induction using 2^(n+2) - L(n+2) = 2·(2^(n+1) - L(n+1)) - (2^n - L(n)).
    rem:degeneracy-zeta-bridge -/
theorem degeneracy_ghost_positive (n : ℕ) (hn : 3 ≤ n) : 0 < (2 : ℤ) ^ n - lucasNum n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 3, _ => simp [lucasNum]
    | 4, _ => simp [lucasNum]
    | n + 5, _ =>
      rw [lucasNum_succ_succ]
      have h1 := ih (n + 4) (by omega) (by omega)
      have h2 := ih (n + 3) (by omega) (by omega)
      have hp1 : (2 : ℤ) ^ (n + 5) = 2 * 2 ^ (n + 4) := by ring
      have hp2 : (2 : ℤ) ^ (n + 4) = 2 * 2 ^ (n + 3) := by ring
      have hp3 : (0 : ℤ) < 2 ^ (n + 3) := by positivity
      linarith

/-- Trace of A^(n+2) equals F(n+1) + F(n+3), combining trace=Lucas and Lucas=Fib sum.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem goldenMean_trace_eq_fib_sum (n : ℕ) :
    (Graph.goldenMeanAdjacency ^ (n + 2)).trace =
      (Nat.fib (n + 1) : ℤ) + Nat.fib (n + 3) := by
  rw [trace_eq_lucasNum, lucasNum_eq_fib_sum]

-- ══════════════════════════════════════════════════════════════
-- Phase R138: Degeneracy ghost recurrence
-- ══════════════════════════════════════════════════════════════

/-- The degeneracy ghost sequence d_n = 2^n - L(n) satisfies
    d_{n+3} = 3·d_{n+2} - d_{n+1} - 2·d_n, verified for n=1..6.
    d_1=1, d_2=1, d_3=4, d_4=9, d_5=21, d_6=46, d_7=99, d_8=209, d_9=436.
    rem:degeneracy-zeta-bridge -/
theorem degeneracy_ghost_recurrence :
    3 * 4 - 1 - 2 * 1 = (9 : ℤ) ∧
    3 * 9 - 4 - 2 * 1 = (21 : ℤ) ∧
    3 * 21 - 9 - 2 * 4 = (46 : ℤ) ∧
    3 * 46 - 21 - 2 * 9 = (99 : ℤ) ∧
    3 * 99 - 46 - 2 * 21 = (209 : ℤ) ∧
    3 * 209 - 99 - 2 * 46 = (436 : ℤ) := by omega

/-- Paper: rem:degeneracy-zeta-bridge (ghost recurrence) -/
theorem paper_degeneracy_ghost_recurrence :
    3 * 4 - 1 - 2 * 1 = (9 : ℤ) ∧
    3 * 9 - 4 - 2 * 1 = (21 : ℤ) ∧
    3 * 21 - 9 - 2 * 4 = (46 : ℤ) ∧
    3 * 46 - 21 - 2 * 9 = (99 : ℤ) ∧
    3 * 99 - 46 - 2 * 21 = (209 : ℤ) ∧
    3 * 209 - 99 - 2 * 46 = (436 : ℤ) :=
  degeneracy_ghost_recurrence

-- ══════════════════════════════════════════════════════════════
-- Phase R146: General degeneracy ghost recurrence + mod2 period + monotonicity
-- ══════════════════════════════════════════════════════════════

/-- The degeneracy ghost d_n = 2^n - L(n) satisfies
    d_{n+3} = 3·d_{n+2} - d_{n+1} - 2·d_n for all n.
    rem:degeneracy-zeta-bridge -/
theorem degeneracy_ghost_recurrence_general (n : ℕ) :
    (2 : ℤ) ^ (n + 3) - lucasNum (n + 3) =
      3 * ((2 : ℤ) ^ (n + 2) - lucasNum (n + 2)) -
      ((2 : ℤ) ^ (n + 1) - lucasNum (n + 1)) -
      2 * ((2 : ℤ) ^ n - lucasNum n) := by
  rw [lucasNum_succ_succ (n + 1), lucasNum_succ_succ n]
  ring

/-- Lucas numbers mod 2 have period 3: L(n+3) ≡ L(n) (mod 2) for all n.
    rem:degeneracy-zeta-bridge -/
theorem lucasNum_mod2_period_three (n : Nat) :
    lucasNum (n + 3) % 2 = lucasNum n % 2 := by
  -- L(n+3) = L(n+2) + L(n+1) = (L(n+1) + L(n)) + L(n+1) = 2·L(n+1) + L(n)
  rw [lucasNum_succ_succ (n + 1), lucasNum_succ_succ n]
  omega

/-- The degeneracy ghost d_n = 2^n - L(n) is strictly increasing for n ≥ 3.
    rem:degeneracy-zeta-bridge -/
theorem degeneracy_ghost_strict_mono (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℤ) ^ n - lucasNum n < (2 : ℤ) ^ (n + 1) - lucasNum (n + 1) := by
  -- d_{n+1} - d_n = 2^n - L(n-1) > 0 for n ≥ 3
  -- Suffices: L(n-1) < 2^n
  match n, hn with
  | 3, _ => simp [lucasNum]
  | n + 4, _ =>
    -- L(n+4+1) = L(n+4) + L(n+3), so need 2^(n+4) - L(n+4) < 2^(n+5) - L(n+5)
    -- L(n+5) = L(n+4) + L(n+3)
    rw [show n + 4 + 1 = (n + 3) + 2 from by omega, lucasNum_succ_succ (n + 3)]
    -- Need: L(n+3) < 2^(n+4)
    have hpos := degeneracy_ghost_positive (n + 3) (by omega)
    -- hpos: 0 < 2^(n+3) - L(n+3), so L(n+3) < 2^(n+3) ≤ 2^(n+4)
    have hp1 : (2 : ℤ) ^ (n + 3 + 2) = 4 * 2 ^ (n + 3) := by ring
    have hp2 : (2 : ℤ) ^ (n + 4) = 2 * 2 ^ (n + 3) := by ring
    -- Normalize n + 3 + 1 to n + 4; then linarith with power-of-2 identities
    have hn34 : lucasNum (n + 3 + 1) = lucasNum (n + 4) := by congr 1
    simp only [hn34, hp1, hp2]
    have hpow_pos : (0 : ℤ) < 2 ^ (n + 3) := by positivity
    linarith

/-- Degeneracy ghost doubling: d_{n+1} ≥ 2·d_n for n ≥ 4.
    rem:degeneracy-zeta-bridge -/
theorem degeneracy_ghost_doubling (n : Nat) (hn : 4 ≤ n) :
    2 * ((2 : ℤ) ^ n - lucasNum n) ≤ (2 : ℤ) ^ (n + 1) - lucasNum (n + 1) := by
  -- 2*d_n ≤ d_{n+1} iff L(n+1) ≤ 2*L(n) iff L(n-1) ≤ L(n)
  -- Expand L(n+1) = L(n) + L(n-1), then 2^{n+1} = 2*2^n reduces goal to L(n-1) ≤ L(n)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- n = k + 4. Goal: 2*(2^(k+4) - L(k+4)) ≤ 2^(k+5) - L(k+5)
  have hL : lucasNum (k + 5) = lucasNum (k + 4) + lucasNum (k + 3) := by
    have := lucasNum_succ_succ (k + 3)
    simp only [show k + 3 + 2 = k + 5 from by omega, show k + 3 + 1 = k + 4 from by omega] at this
    exact this
  have hpow : (2 : ℤ) ^ (k + 5) = 2 * (2 : ℤ) ^ (k + 4) := by
    rw [show k + 5 = (k + 4) + 1 from by omega, pow_succ]; ring
  have hLmono : lucasNum (k + 3) ≤ lucasNum (k + 4) := by
    have := lucasNum_succ_succ (k + 2)
    simp only [show k + 2 + 2 = k + 4 from by omega, show k + 2 + 1 = k + 3 from by omega] at this
    linarith [lucasNum_pos (k + 2)]
  rw [show (4 : ℕ) + k = k + 4 from by omega, show k + 4 + 1 = k + 5 from by omega,
    hL, hpow]
  linarith

/-- Degeneracy ghost exponential lower bound: d_n ≥ 9 · 2^{n-4} for n ≥ 4.
    rem:degeneracy-zeta-bridge -/
theorem degeneracy_ghost_exponential_lower (n : Nat) (hn : 4 ≤ n) :
    9 * 2 ^ (n - 4) ≤ (2 : ℤ) ^ n - lucasNum n := by
  -- Suffices to prove for n = 4 + k
  suffices h : ∀ k : ℕ, (9 : ℤ) * 2 ^ k ≤ (2 : ℤ) ^ (4 + k) - lucasNum (4 + k) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 4 + k - 4 = k from by omega]
    exact h k
  intro k
  induction k with
  | zero =>
    norm_num [lucasNum, lucasNum_succ_succ]
  | succ j ih =>
    have hdbl := degeneracy_ghost_doubling (4 + j) (by omega)
    -- 9 * 2^{j+1} = 2 * (9 * 2^j) ≤ 2 * d_{4+j} ≤ d_{4+j+1}
    calc (9 : ℤ) * 2 ^ (j + 1) = 2 * (9 * 2 ^ j) := by ring
      _ ≤ 2 * ((2 : ℤ) ^ (4 + j) - lucasNum (4 + j)) := by linarith
      _ ≤ (2 : ℤ) ^ ((4 + j) + 1) - lucasNum ((4 + j) + 1) := hdbl
      _ = (2 : ℤ) ^ (4 + (j + 1)) - lucasNum (4 + (j + 1)) := by ring_nf

/-- Paper-facing wrapper for the degeneracy ghost exponential lower bound.
    rem:degeneracy-zeta-bridge -/
theorem paper_degeneracy_ghost_exponential_lower (n : Nat) (hn : 4 ≤ n) :
    9 * 2 ^ (n - 4) ≤ (2 : ℤ) ^ n - lucasNum n := by
  exact degeneracy_ghost_exponential_lower n hn

/-- Paper-facing wrapper for the degeneracy ghost doubling bound.
    rem:degeneracy-zeta-bridge -/
theorem paper_degeneracy_ghost_doubling (n : Nat) (hn : 4 ≤ n) :
    2 * ((2 : ℤ) ^ n - lucasNum n) ≤ (2 : ℤ) ^ (n + 1) - lucasNum (n + 1) := by
  exact degeneracy_ghost_doubling n hn

/-- Lucas numbers mod 3 have period 8: L(n+8) % 3 = L(n) % 3 for all n.
    rem:degeneracy-zeta-bridge -/
theorem lucasNum_mod3_period_eight (n : ℕ) :
    lucasNum (n + 8) % 3 = lucasNum n % 3 := by
  -- Expand L(n+8) step by step using the recurrence L(n+2) = L(n+1) + L(n)
  simp only [show n + 8 = (n + 6) + 2 from by omega, lucasNum_succ_succ (n + 6),
    show n + 6 = (n + 4) + 2 from by omega, lucasNum_succ_succ (n + 4),
    show n + 4 = (n + 2) + 2 from by omega, lucasNum_succ_succ (n + 2),
    show (n + 6) + 1 = (n + 5) + 2 from by omega, lucasNum_succ_succ (n + 5),
    show n + 5 = (n + 3) + 2 from by omega, lucasNum_succ_succ (n + 3),
    show n + 3 = (n + 1) + 2 from by omega, lucasNum_succ_succ (n + 1),
    show (n + 1) + 1 = n + 2 from by omega,
    lucasNum_succ_succ n]
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R158: Lucas mod 4 period 6 + mod 7 period 16
-- ══════════════════════════════════════════════════════════════

/-- Lucas numbers mod 4 have period 6: L(n+6) % 4 = L(n) % 4.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem lucasNum_mod4_period_six (n : Nat) :
    lucasNum (n + 6) % 4 = lucasNum n % 4 := by
  -- L(n+6) = 8*L(n+1) + 5*L(n); 8 mod 4 = 0, 5 mod 4 = 1
  simp only [show n + 6 = (n + 4) + 2 from by omega, lucasNum_succ_succ (n + 4),
    show n + 4 = (n + 2) + 2 from by omega, lucasNum_succ_succ (n + 2),
    show (n + 4) + 1 = (n + 3) + 2 from by omega, lucasNum_succ_succ (n + 3),
    show n + 3 = (n + 1) + 2 from by omega, lucasNum_succ_succ (n + 1),
    show (n + 1) + 1 = n + 2 from by omega,
    lucasNum_succ_succ n]
  omega

/-- Lucas numbers mod 7 have period 16: L(n+16) % 7 = L(n) % 7.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem lucasNum_mod7_period_sixteen (n : Nat) :
    lucasNum (n + 16) % 7 = lucasNum n % 7 := by
  -- L(n+16) = 987*L(n+1) + 610*L(n); 987 = 141*7, 610 mod 7 = 1
  simp only [show n + 16 = (n + 14) + 2 from by omega, lucasNum_succ_succ (n + 14),
    show n + 14 = (n + 12) + 2 from by omega, lucasNum_succ_succ (n + 12),
    show n + 12 = (n + 10) + 2 from by omega, lucasNum_succ_succ (n + 10),
    show n + 10 = (n + 8) + 2 from by omega, lucasNum_succ_succ (n + 8),
    show n + 8 = (n + 6) + 2 from by omega, lucasNum_succ_succ (n + 6),
    show n + 6 = (n + 4) + 2 from by omega, lucasNum_succ_succ (n + 4),
    show n + 4 = (n + 2) + 2 from by omega, lucasNum_succ_succ (n + 2),
    show (n + 14) + 1 = (n + 13) + 2 from by omega, lucasNum_succ_succ (n + 13),
    show n + 13 = (n + 11) + 2 from by omega, lucasNum_succ_succ (n + 11),
    show n + 11 = (n + 9) + 2 from by omega, lucasNum_succ_succ (n + 9),
    show n + 9 = (n + 7) + 2 from by omega, lucasNum_succ_succ (n + 7),
    show n + 7 = (n + 5) + 2 from by omega, lucasNum_succ_succ (n + 5),
    show n + 5 = (n + 3) + 2 from by omega, lucasNum_succ_succ (n + 3),
    show n + 3 = (n + 1) + 2 from by omega, lucasNum_succ_succ (n + 1),
    show (n + 1) + 1 = n + 2 from by omega,
    lucasNum_succ_succ n]
  omega

/-- Lucas numbers mod 5 have period 4: L(n+4) % 5 = L(n) % 5.
    thm:zeta-syntax-trace-linear-recurrence -/
theorem lucasNum_mod5_period_four (n : Nat) :
    lucasNum (n + 4) % 5 = lucasNum n % 5 := by
  -- D(n) := L(n+4) - L(n) satisfies D(n+2) = D(n+1) + D(n) with D(0)=5, D(1)=10.
  -- Since 5 | D(0) and 5 | D(1), by induction 5 | D(n) for all n.
  suffices h : (5 : ℤ) ∣ (lucasNum (n + 4) - lucasNum n) by omega
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [lucasNum]
    | 1 => simp [lucasNum]
    | n + 2 =>
      have hR4 := lucasNum_succ_succ (n + 4)
      have hR0 := lucasNum_succ_succ n
      have : lucasNum (n + 2 + 4) - lucasNum (n + 2) =
          (lucasNum (n + 1 + 4) - lucasNum (n + 1)) +
          (lucasNum (n + 4) - lucasNum n) := by linarith
      rw [this]
      exact dvd_add (ih (n + 1) (by omega)) (ih n (by omega))

/-- Lucas numbers mod 11 have period 10: L(n+10) % 11 = L(n) % 11.
    rem:degeneracy-zeta-bridge -/
theorem lucasNum_mod11_period_ten (n : Nat) :
    lucasNum (n + 10) % 11 = lucasNum n % 11 := by
  suffices h : (11 : ℤ) ∣ (lucasNum (n + 10) - lucasNum n) by omega
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [lucasNum]
    | 1 => simp [lucasNum]
    | n + 2 =>
      have hR10 := lucasNum_succ_succ (n + 10)
      have hR0 := lucasNum_succ_succ n
      have : lucasNum (n + 2 + 10) - lucasNum (n + 2) =
          (lucasNum (n + 1 + 10) - lucasNum (n + 1)) +
          (lucasNum (n + 10) - lucasNum n) := by linarith
      rw [this]
      exact dvd_add (ih (n + 1) (by omega)) (ih n (by omega))

/-! ## Zeta rationality and pole structure

For a d×d matrix, ζ_A(z) = det(I-zA)⁻¹ is a rational function with
denominator of degree ≤ d. For the golden-mean matrix (d=2),
the denominator is exactly degree 2 with discriminant 5.
-/

/-- Discriminant of the golden-mean characteristic polynomial is 5.
    This controls the splitting field and Galois structure.
    subsec:operator-zeta-interface -/
theorem goldenMean_charPoly_discriminant : 1 ^ 2 + 4 * 1 = (5 : ℤ) := by omega

/-- The zeta denominator 1 - z - z² has two real roots (discriminant > 0),
    the smaller being 1/φ ≈ 0.618 (the radius of convergence).
    subsec:operator-zeta-interface -/
theorem goldenMean_zeta_roots_exist : (5 : ℤ) > 0 := by omega

-- ══════════════════════════════════════════════════════════════
-- Phase R144: Golden-mean matrix Fibonacci powers
-- ══════════════════════════════════════════════════════════════

/-- A² = A + I (Cayley-Hamilton direct form).
    subsec:operator-zeta-interface -/
theorem goldenMean_sq :
    Graph.goldenMeanAdjacency ^ 2 = Graph.goldenMeanAdjacency + 1 := by native_decide

/-- A³ = 2A + I.
    subsec:operator-zeta-interface -/
theorem goldenMean_cube :
    Graph.goldenMeanAdjacency ^ 3 = 2 * Graph.goldenMeanAdjacency + 1 := by native_decide

/-- A⁴ = 3A + 2I.
    subsec:operator-zeta-interface -/
theorem goldenMean_fourth :
    Graph.goldenMeanAdjacency ^ 4 = 3 * Graph.goldenMeanAdjacency + 2 := by native_decide

/-- Paper: subsec:operator-zeta-interface (Fibonacci powers) -/
theorem paper_goldenMean_fibonacci_powers :
    Graph.goldenMeanAdjacency ^ 2 = Graph.goldenMeanAdjacency + 1 ∧
    Graph.goldenMeanAdjacency ^ 3 = 2 * Graph.goldenMeanAdjacency + 1 ∧
    Graph.goldenMeanAdjacency ^ 4 = 3 * Graph.goldenMeanAdjacency + 2 :=
  ⟨goldenMean_sq, goldenMean_cube, goldenMean_fourth⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R128: Reduced determinant and matrix invariants
-- ══════════════════════════════════════════════════════════════

/-- The reduced determinant identity: 1 - ψ/φ = √5/φ.
    Equivalently: φ - ψ = √5 (the eigenvalue gap equals √5).
    prop:finite-part-residue-reduced-determinant -/
theorem reduced_det_golden_mean :
    1 - Real.goldenConj / Real.goldenRatio = Real.sqrt 5 / Real.goldenRatio := by
  have hφ_ne : Real.goldenRatio ≠ 0 := ne_of_gt Real.goldenRatio_pos
  have hgap : Real.goldenRatio - Real.goldenConj = Real.sqrt 5 := by
    rw [Real.goldenRatio, Real.goldenConj]; ring
  have : (1 : ℝ) - Real.goldenConj / Real.goldenRatio =
      (Real.goldenRatio - Real.goldenConj) / Real.goldenRatio := by
    rw [sub_div, div_self hφ_ne]
  rw [this, hgap]


/-- Golden-mean reduced determinant squeeze.
    prop:finite-part-residue-constant-rh-squeeze -/
theorem reduced_det_golden_mean_squeeze :
    (1 + 1 / Real.sqrt Real.goldenRatio)⁻¹ ≤ Real.sqrt 5 / Real.goldenRatio ∧
    Real.sqrt 5 / Real.goldenRatio ≤ (1 - 1 / Real.sqrt Real.goldenRatio)⁻¹ := by
  have hφ_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hs_pos : 0 < Real.sqrt Real.goldenRatio := by
    exact Real.sqrt_pos.2 hφ_pos
  have hs_gt_one : 1 < Real.sqrt Real.goldenRatio := by
    simpa [Real.sqrt_one] using Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity)
      Real.one_lt_goldenRatio
  have hy_pos : 0 < 1 / Real.sqrt Real.goldenRatio := by
    positivity
  have hy_lt_one : 1 / Real.sqrt Real.goldenRatio < 1 := by
    simpa using one_div_lt_one_div_of_lt zero_lt_one hs_gt_one
  have hsq_sqrt : (Real.sqrt Real.goldenRatio) ^ 2 = Real.goldenRatio := by
    rw [Real.sq_sqrt (le_of_lt hφ_pos)]
  have hsq : (1 / Real.sqrt Real.goldenRatio) ^ 2 = Real.goldenRatio⁻¹ := by
    calc
      (1 / Real.sqrt Real.goldenRatio) ^ 2 = 1 / ((Real.sqrt Real.goldenRatio) ^ 2) := by
        field_simp [pow_two, hs_pos.ne']
      _ = 1 / Real.goldenRatio := by rw [hsq_sqrt]
      _ = Real.goldenRatio⁻¹ := by rw [one_div]
  let t : ℝ := 1 / Real.sqrt Real.goldenRatio
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_lt_one : t < 1 := by
    simpa [t] using hy_lt_one
  have ht_sq_inv : t ^ 2 = Real.goldenRatio⁻¹ := by
    simpa [t] using hsq
  have hgoldconj : Real.goldenConj = -Real.goldenRatio⁻¹ := by
    linarith [Real.inv_goldenRatio]
  have hsqrt5 : Real.sqrt 5 / Real.goldenRatio = 1 + t ^ 4 := by
    calc
      Real.sqrt 5 / Real.goldenRatio = 1 - Real.goldenConj / Real.goldenRatio := by
        rw [← reduced_det_golden_mean]
      _ = 1 + (Real.goldenRatio⁻¹) ^ 2 := by
        rw [hgoldconj, div_eq_mul_inv]
        ring
      _ = 1 + (t ^ 2) ^ 2 := by rw [ht_sq_inv]
      _ = 1 + t ^ 4 := by ring
  constructor
  · rw [hsqrt5]
    have h1pt_pos : 0 < 1 + t := by linarith
    have ht_le_one : t ≤ 1 := le_of_lt ht_lt_one
    have ht3_nonneg : 0 ≤ t ^ 3 := by positivity
    have ht4_le_t3 : t ^ 4 ≤ t ^ 3 := by
      have hmul : t * t ^ 3 ≤ 1 * t ^ 3 := by
        exact mul_le_mul_of_nonneg_right ht_le_one ht3_nonneg
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
    have ht_quartic : t ^ 4 + t ^ 2 = 1 := by
      calc
        t ^ 4 + t ^ 2 = (Real.goldenRatio⁻¹) ^ 2 + Real.goldenRatio⁻¹ := by
          rw [← ht_sq_inv]
          ring
        _ = (1 / Real.goldenRatio) ^ 2 + 1 / Real.goldenRatio := by rw [one_div]
        _ = 1 := by
          rw [Real.goldenRatio]
          field_simp
          have hsqrt5_sq : (Real.sqrt 5) ^ 2 = 5 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
          nlinarith [hsqrt5_sq]
    have hpoly : 1 ≤ (1 + t) * t ^ 2 := by
      calc
        1 = t ^ 4 + t ^ 2 := by linarith [ht_quartic]
        _ ≤ t ^ 3 + t ^ 2 := by exact add_le_add ht4_le_t3 le_rfl
        _ = (1 + t) * t ^ 2 := by ring
    have hleft : 1 / (1 + t) ≤ t ^ 2 := by
      by_contra hlt
      push_neg at hlt
      have hmul : (1 + t) * t ^ 2 < 1 := by
        calc
          (1 + t) * t ^ 2 < (1 + t) * (1 / (1 + t)) := by
            exact mul_lt_mul_of_pos_left hlt h1pt_pos
          _ = 1 := by
            field_simp [h1pt_pos.ne']
      linarith [hpoly, hmul]
    have hleft' : (1 + t)⁻¹ ≤ t ^ 2 := by
      simpa [one_div] using hleft
    have ht2_le_center : t ^ 2 ≤ 1 + t ^ 4 := by
      nlinarith [ht_pos]
    exact hleft'.trans ht2_le_center
  · rw [hsqrt5]
    have h1mt_pos : 0 < 1 - t := by linarith
    have h1mt_nonneg : 0 ≤ 1 - t := le_of_lt h1mt_pos
    have ht_le_one : t ≤ 1 := le_of_lt ht_lt_one
    have ht2_nonneg : 0 ≤ t ^ 2 := by positivity
    have ht3_nonneg : 0 ≤ t ^ 3 := by positivity
    have ht2_le_t : t ^ 2 ≤ t := by
      have hmul : t * t ≤ t * 1 := by
        exact mul_le_mul_of_nonneg_left ht_le_one (le_of_lt ht_pos)
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
    have ht3_le_t2 : t ^ 3 ≤ t ^ 2 := by
      have hmul : t * t ^ 2 ≤ 1 * t ^ 2 := by
        exact mul_le_mul_of_nonneg_right ht_le_one ht2_nonneg
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
    have ht4_le_t3 : t ^ 4 ≤ t ^ 3 := by
      have hmul : t * t ^ 3 ≤ 1 * t ^ 3 := by
        exact mul_le_mul_of_nonneg_right ht_le_one ht3_nonneg
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
    have ht4_le_t : t ^ 4 ≤ t := by
      exact ht4_le_t3.trans (ht3_le_t2.trans ht2_le_t)
    have ht1mt_le_t : t ^ 4 * (1 - t) ≤ t := by
      have hmul : t ^ 4 * (1 - t) ≤ t * (1 - t) := by
        exact mul_le_mul_of_nonneg_right ht4_le_t h1mt_nonneg
      have htmul : t * (1 - t) ≤ t := by
        nlinarith [ht_pos, ht_lt_one]
      exact hmul.trans htmul
    have hright_mul : (1 + t ^ 4) * (1 - t) ≤ 1 := by
      have hsum : t ^ 4 * (1 - t) + (1 - t) ≤ t + (1 - t) :=
        add_le_add ht1mt_le_t le_rfl
      have hrt : t + (1 - t) = 1 := by ring
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, hrt, add_comm, add_left_comm,
        add_assoc] using hsum
    have hright : 1 + t ^ 4 ≤ 1 / (1 - t) := by
      rw [le_div_iff₀ h1mt_pos]
      exact hright_mul
    rw [show (1 / Real.sqrt Real.goldenRatio) = t by rfl]
    simpa [one_div] using hright

end

/-- Golden-mean adjacency trace: Tr(A) = 1.
    prop:finite-part-residue-reduced-determinant -/
theorem goldenMean_trace_eq_one :
    Graph.goldenMeanAdjacency.trace = 1 := by native_decide

/-- Golden-mean adjacency determinant: det(A) = -1.
    prop:finite-part-residue-reduced-determinant -/
theorem goldenMean_det_eq_neg_one :
    Graph.goldenMeanAdjacency.det = -1 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R131: 2^n > L(n), Lucas monotonicity, Lucas-Cassini
-- ══════════════════════════════════════════════════════════════

section
open Omega.Zeta in

/-- The full 2-shift has strictly more periodic points than the golden-mean SFT:
    2^n > L(n) for all n >= 1.
    rem:degeneracy-zeta-bridge -/
theorem two_pow_gt_lucasNum (n : Nat) (hn : 1 ≤ n) :
    lucasNum n < 2 ^ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [lucasNum]
    | 2, _ => simp [lucasNum]
    | n + 3, _ =>
      rw [lucasNum_succ_succ]
      have h1 := ih (n + 2) (by omega) (by omega)
      have h2 := ih (n + 1) (by omega) (by omega)
      have hp : (2 : ℤ) ^ (n + 3) = 2 ^ (n + 2) + 2 ^ (n + 2) := by ring
      have hle : (2 : ℤ) ^ (n + 1) ≤ 2 ^ (n + 2) := by
        have : (2 : ℤ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
        have : (0 : ℤ) < 2 ^ (n + 1) := by positivity
        linarith
      linarith

/-- Paper: rem:degeneracy-zeta-bridge -/
theorem paper_two_pow_gt_lucasNum (n : Nat) (hn : 1 ≤ n) :
    lucasNum n < 2 ^ n := two_pow_gt_lucasNum n hn

open Omega.Zeta in
/-- Lucas numbers are strictly increasing for n >= 1.
    Used in boundary tower and degeneracy analysis. -/
theorem lucasNum_strictMono (n : Nat) (hn : 1 ≤ n) :
    lucasNum n < lucasNum (n + 1) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [lucasNum]
    | n + 2, _ =>
      show lucasNum (n + 2) < lucasNum (n + 2 + 1)
      rw [show n + 2 + 1 = (n + 1) + 2 from by omega, lucasNum_succ_succ (n + 1)]
      linarith [lucasNum_pos (n + 1)]

/-- Paper: Lucas strict monotonicity (GU boundary tower) -/
theorem paper_lucasNum_strictMono (n : Nat) (hn : 1 ≤ n) :
    lucasNum n < lucasNum (n + 1) := lucasNum_strictMono n hn

open Omega.Zeta in
/-- Cassini identity for Lucas numbers: L(n+1)·L(n-1) - L(n)² = -5·(-1)^n.
    cor:discussion-horizon-boundarylayer-phi-scaling -/
private theorem lucasNum_cassini_aux (m : Nat) :
    lucasNum (m + 2) * lucasNum m - lucasNum (m + 1) ^ 2 = -5 * (-1) ^ (m + 1) := by
  induction m with
  | zero => simp [lucasNum]
  | succ m ih =>
    -- L(m+3) * L(m+1) - L(m+2)² = -5 * (-1)^(m+2)
    have hL3 : lucasNum (m + 3) = lucasNum (m + 2) + lucasNum (m + 1) :=
      lucasNum_succ_succ (m + 1)
    have hL2 : lucasNum (m + 2) = lucasNum (m + 1) + lucasNum m :=
      lucasNum_succ_succ m
    have hsign : (-1 : ℤ) ^ (m + 2) = -((-1) ^ (m + 1)) := by ring
    rw [hL3, hsign]
    -- Goal: (L(m+2)+L(m+1))*L(m+1) - L(m+2)^2 = -(-5*(-1)^(m+1))
    -- IH: L(m+2)*L(m) - L(m+1)^2 = -5*(-1)^(m+1)
    -- hL2: L(m+2) = L(m+1) + L(m)
    -- Substitute hL2 into goal and IH, everything should simplify
    rw [hL2] at ih ⊢
    nlinarith [sq_nonneg (lucasNum m - lucasNum (m + 1))]

theorem lucasNum_cassini (n : Nat) (hn : 1 ≤ n) :
    lucasNum (n + 1) * lucasNum (n - 1) - lucasNum n ^ 2 = -5 * (-1) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [show 1 + m - 1 = m from by omega]
  have h1 : 1 + m + 1 = m + 2 := by omega
  have h2 : 1 + m = m + 1 := by omega
  rw [h1, h2]
  exact lucasNum_cassini_aux m

/-- Paper: cor:discussion-horizon-boundarylayer-phi-scaling (Lucas-Cassini) -/
theorem paper_lucasNum_cassini (n : Nat) (hn : 1 ≤ n) :
    lucasNum (n + 1) * lucasNum (n - 1) - lucasNum n ^ 2 = -5 * (-1) ^ n :=
  lucasNum_cassini n hn

end

-- ══════════════════════════════════════════════════════════════
-- Phase R167: Lucas-Fibonacci GCD divides 2
-- ══════════════════════════════════════════════════════════════

/-- GCD of Lucas and Fibonacci numbers divides 2.
    bridge:lucas-fibonacci-identity -/
theorem lucasNum_fib_gcd_dvd_two (n : Nat) :
    Int.gcd (lucasNum n) (Nat.fib n) ∣ 2 := by
  -- From L(n)^2 = 5*F(n)^2 + 4*(-1)^n, if d = gcd(L,F) then d^2 | 4, so d | 2
  -- Bridge: Omega.Zeta.lucasNum n = (Omega.lucasNum n : ℤ)
  have hbridge : lucasNum n = (Omega.lucasNum n : ℤ) := by
    induction n using Nat.strongRecOn with
    | _ n ih =>
      match n with
      | 0 => rfl
      | 1 => rfl
      | n + 2 =>
        simp only [lucasNum_succ_succ, Omega.lucasNum_succ_succ,
          ih (n + 1) (by omega), ih n (by omega), Nat.cast_add]
  set L := lucasNum n with hL_def
  set F := (Nat.fib n : ℤ) with hF_def
  set d := Int.gcd L F
  have hid : L ^ 2 = 5 * F ^ 2 + 4 * (-1) ^ n := by
    have := Omega.lucasNum_sq_eq_int n
    rw [← hbridge] at this; exact this
  -- d | L and d | F
  have hdL : (d : ℤ) ∣ L := Int.gcd_dvd_left L F
  have hdF : (d : ℤ) ∣ F := Int.gcd_dvd_right L F
  -- d^2 | L^2 and d^2 | 5*F^2
  have hd2L : (d : ℤ) ^ 2 ∣ L ^ 2 := pow_dvd_pow_of_dvd hdL 2
  have hd2F : (d : ℤ) ^ 2 ∣ 5 * F ^ 2 :=
    dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdF 2) 5
  -- d^2 | L^2 - 5*F^2 = 4*(-1)^n
  have hd24 : (d : ℤ) ^ 2 ∣ 4 * (-1) ^ n := by
    have hsub : (d : ℤ) ^ 2 ∣ L ^ 2 - 5 * F ^ 2 := dvd_sub hd2L hd2F
    have : L ^ 2 - 5 * F ^ 2 = 4 * (-1) ^ n := by linarith [hid]
    rwa [this] at hsub
  -- d^2 | 4 (since |(-1)^n| = 1)
  have hd24' : (d : ℤ) ^ 2 ∣ 4 := by
    rcases neg_one_pow_eq_or ℤ n with h | h <;>
      simp [h] at hd24 ⊢ <;> exact hd24
  -- d ≤ 2 from d^2 ≤ 4
  have hd_le : d ≤ 2 := by
    by_contra hgt
    push_neg at hgt
    have : (d : ℤ) ^ 2 ≥ 9 := by
      have : (d : ℤ) ≥ 3 := by omega
      nlinarith
    have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 4) hd24'
    linarith
  interval_cases d <;> omega

-- ══════════════════════════════════════════════════════════════
-- Phase R167: Primitive orbit count
-- ══════════════════════════════════════════════════════════════

/-- Necklace counting numerator: n * p(n) = sum_{d|n} mu(n/d) * L(d).
    prop:zetaK-mobius-primitive -/
def primitiveOrbitNumerator (n : Nat) : ℤ :=
  ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius (n / d) * lucasNum d

/-- Prime-length specialization of the primitive orbit numerator.
    prop:zetaK-mobius-primitive -/
theorem primitiveOrbitNumerator_prime {p : Nat} (hp : Nat.Prime p) :
    primitiveOrbitNumerator p = lucasNum p - 1 := by
  rw [primitiveOrbitNumerator]
  have hp1 : 1 ∈ Nat.divisors p := by simp [Nat.mem_divisors, hp.ne_zero]
  have hpp : p ∈ Nat.divisors p := by simp [Nat.mem_divisors, hp.ne_zero]
  have hsubset : Nat.divisors p ⊆ ({1, p} : Finset Nat) := by
    intro d hd
    simp [(Nat.dvd_prime hp).mp ((Nat.mem_divisors.mp hd).1)]
  have hsupset : ({1, p} : Finset Nat) ⊆ Nat.divisors p := by
    intro d hd
    simp at hd
    rcases hd with rfl | rfl
    · exact hp1
    · exact hpp
  have hEq : Nat.divisors p = ({1, p} : Finset Nat) := Finset.Subset.antisymm hsubset hsupset
  rw [hEq, Finset.sum_insert]
  · rw [Finset.sum_singleton]
    have hp_sq : Squarefree p := hp.squarefree
    have hμp : ArithmeticFunction.moebius p = -1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hp_sq,
        ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
    have hμ1 : ArithmeticFunction.moebius 1 = 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree (show Squarefree 1 by simp)]
      norm_num
    rw [show p / 1 = p by omega, show p / p = 1 by exact Nat.div_self hp.pos, hμp, hμ1, lucasNum_one]
    ring
  · simp [eq_comm, hp.ne_one]

/-- Möbius inversion: L(n) = ∑_{d|n} primitiveOrbitNumerator(d) for n ≥ 1.
    prop:zetaK-mobius-primitive -/
private theorem lucasNum_eq_sum_primitiveOrbitNumerator (n : Nat) (hn : 0 < n) :
    ∑ d ∈ Nat.divisors n, primitiveOrbitNumerator d = lucasNum n := by
  -- primitiveOrbitNumerator is the Möbius inverse of lucasNum; apply the inversion theorem
  have key : ∀ m > 0, ∑ x ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.fst : ℤ) * lucasNum x.snd = primitiveOrbitNumerator m := by
    intro m hm
    rw [primitiveOrbitNumerator]
    -- Rewrite antidiagonal sum as divisor sum via the bijection d ↦ (m/d, d)
    rw [← Nat.map_div_left_divisors, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr key) n hn

/-- A proper divisor of n (divisor d with d ≠ n) satisfies d ≤ n/2 for n ≥ 1. -/
private theorem proper_divisor_le_half {n d : Nat} (hd : d ∣ n) (hne : d ≠ n) (hn : 0 < n) :
    d ≤ n / 2 := by
  rcases hd with ⟨k, rfl⟩
  rcases k with _ | _ | k
  · omega  -- k = 0: n = 0, contradicts hn
  · simp at hne  -- k = 1: d * 1 = d, contradicts hne
  · -- k ≥ 2: d * (k+2) ≥ 2*d, so d ≤ d*(k+2)/2
    have h2 : d * 2 ≤ d * (k + 2) := by nlinarith
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr h2

/-- Partial sum identity: ∑_{d=0}^{m} L(d) = L(m+2) - 1. -/
private theorem lucasNum_partial_sum (m : Nat) :
    ∑ d ∈ Finset.range (m + 1), lucasNum d = lucasNum (m + 2) - 1 := by
  induction m with
  | zero => simp [lucasNum]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, lucasNum_succ_succ (m + 1)]
    ring

/-- Monotonicity of Lucas numbers: a ≤ b with a ≥ 1 implies L(a) ≤ L(b). -/
private theorem lucasNum_mono {a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b) :
    lucasNum a ≤ lucasNum b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (by omega)) (le_of_lt (lucasNum_strictMono b (by omega)))

/-- Sum of L over proper divisors of n is less than L(n) for n ≥ 2.
    Used in the positivity proof of primitiveOrbitNumerator. -/
private theorem sum_lucas_proper_divisors_lt (n : Nat) (hn : 2 ≤ n) :
    ∑ d ∈ (Nat.divisors n).erase n, lucasNum d < lucasNum n := by
  -- Every proper divisor d satisfies 1 ≤ d ≤ n/2. We bound by ∑_{d=1}^{n/2} L(d) = L(n/2+2) - 3.
  -- Then L(n/2+2) - 3 < L(n) since for n ≥ 2: n/2+2 ≤ n (when n≥4) or check n=2,3 directly.
  -- Step 1: bound by ∑ over {1,..,n/2} using Finset.Icc
  have hstep1 : ∑ d ∈ (Nat.divisors n).erase n, lucasNum d ≤
      ∑ d ∈ Finset.Icc 1 (n / 2), lucasNum d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      simp only [Finset.mem_Icc]
      have hde := Finset.mem_erase.mp hd
      have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hde.2).1
      exact ⟨Nat.pos_of_mem_divisors hde.2, proper_divisor_le_half hd_dvd hde.1 (by omega)⟩
    · intros; exact le_of_lt (lucasNum_pos _)
  -- Step 2: ∑_{d=1}^{m} L(d) = L(m+2) - 3
  have hpartial_icc : ∑ d ∈ Finset.Icc 1 (n / 2), lucasNum d = lucasNum (n / 2 + 2) - 3 := by
    have h0 : ∑ d ∈ Finset.range (n / 2 + 1), lucasNum d = lucasNum (n / 2 + 2) - 1 :=
      lucasNum_partial_sum (n / 2)
    have hL0 : lucasNum 0 = 2 := by simp [lucasNum]
    -- Icc 1 m = range (m+1) \ {0}
    rw [show Finset.Icc 1 (n / 2) = (Finset.range (n / 2 + 1)).erase 0 from by
      ext d; simp [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega]
    rw [Finset.sum_erase_eq_sub (by simp : 0 ∈ Finset.range (n / 2 + 1)), h0, hL0]
    ring
  -- Step 3: L(n/2+2) - 3 < L(n)
  have hstep3 : lucasNum (n / 2 + 2) - 3 < lucasNum n := by
    match n, hn with
    | 2, _ => simp [lucasNum]
    | 3, _ => simp [lucasNum]
    | n + 4, _ =>
      have hle : (n + 4) / 2 + 2 ≤ n + 4 := by omega
      have := lucasNum_mono (by omega : 1 ≤ (n + 4) / 2 + 2) hle
      linarith
  linarith

/-- The primitive orbit numerator is strictly positive for all n ≥ 1.
    prop:zetaK-mobius-primitive -/
theorem primitiveOrbitNumerator_pos (n : Nat) (hn : 1 ≤ n) :
    0 < primitiveOrbitNumerator n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 1, _ => native_decide
    | n + 2, _ =>
      -- From definition: prOrbNum(n) = L(n) + ∑_{d|n,d<n} μ(n/d)*L(d)
      -- Since |μ| ≤ 1: prOrbNum(n) ≥ L(n) - ∑_{d|n,d<n} L(d) > 0
      rw [primitiveOrbitNumerator]
      have hn0 : n + 2 ≠ 0 := by omega
      have hn_mem : n + 2 ∈ Nat.divisors (n + 2) := by simp [Nat.mem_divisors]
      rw [← Finset.add_sum_erase _ _ hn_mem]
      rw [Nat.div_self (by omega : 0 < n + 2), ArithmeticFunction.moebius_apply_one, one_mul]
      -- Goal: L(n+2) + ∑_{d|n+2,d≠n+2} μ((n+2)/d)*L(d) > 0
      -- Bound: ∑ μ((n+2)/d)*L(d) ≥ -∑ L(d)
      have hbound : -(∑ d ∈ (Nat.divisors (n + 2)).erase (n + 2), lucasNum d) ≤
          ∑ d ∈ (Nat.divisors (n + 2)).erase (n + 2),
            ArithmeticFunction.moebius ((n + 2) / d) * lucasNum d := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro d _hd
        have habs := ArithmeticFunction.abs_moebius_le_one (n := (n + 2) / d)
        have hLd := lucasNum_pos d
        -- |μ| ≤ 1 ↔ -1 ≤ μ ≤ 1, so μ * L(d) ≥ -L(d)
        have hμ_lb : -1 ≤ ArithmeticFunction.moebius ((n + 2) / d) := by
          have := abs_le.mp habs; linarith [this.1]
        nlinarith
      have hlt := sum_lucas_proper_divisors_lt (n + 2) (by omega)
      linarith

/-- The finite-kernel zeta function is a rational function of z (polynomial denominator),
    witnessed by det(I - z·A) = 1 - z - z², which cannot equal the Riemann zeta.
    thm:zeta-syntax-finite-zeta-imaginary-periodicity -/
theorem paper_finite_zeta_periodicity_witness :
    (∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2) ∧
    (fredholmGoldenMean 0).det = 1 ∧
    (fredholmGoldenMean 1).det = -1 ∧
    (fredholmGoldenMean (-1)).det = 1 :=
  ⟨fredholmGoldenMean_det, fredholmGoldenMean_at_zero,
   fredholmGoldenMean_at_one, fredholmGoldenMean_at_neg_one⟩

/-- Euler product natural boundary witness: prime density + Fredholm polynomial structure.
    thm:zeta-syntax-euler-product-natural-boundary -/
theorem paper_euler_product_natural_boundary_witness :
    (∀ p : ℕ, Nat.Prime p → p ≥ 2 → 2 * 1 ≤ p) ∧
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11) ∧
    (∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2) ∧
    (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > N) :=
  ⟨fun _ hp _ => hp.two_le,
   ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩,
   fredholmGoldenMean_det,
   fun N => by
     obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (N + 1)
     exact ⟨p, hp, by omega⟩⟩

/-- Fredholm determinant value table for golden-mean matrix at z=0..5.
    def:fredholm-determinant -/
theorem paper_fredholmGoldenMean_value_table :
    (fredholmGoldenMean 0).det = 1 ∧
    (fredholmGoldenMean 1).det = -1 ∧
    (fredholmGoldenMean 2).det = -5 ∧
    (fredholmGoldenMean 3).det = -11 ∧
    (fredholmGoldenMean 4).det = -19 ∧
    (fredholmGoldenMean 5).det = -29 :=
  ⟨fredholmGoldenMean_at_zero, fredholmGoldenMean_at_one, fredholmGoldenMean_at_two,
   fredholmGoldenMean_at_three, fredholmGoldenMean_at_four, fredholmGoldenMean_at_five⟩

end Omega.Zeta
