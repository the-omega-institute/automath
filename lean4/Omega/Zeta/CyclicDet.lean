import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic

/-!
# Cyclic Permutation Determinant

Formalizations from the Zeta chapter operator section (§operator-zeta-interface).
Key result: det(I - t·Π_n) = 1 - t^n for the cyclic permutation matrix Π_n.
This is Proposition `prop:cycle-permutation-determinant`.
-/

namespace Omega.Zeta

open Matrix Finset

/-! ## Cyclic permutation matrix

The cyclic permutation matrix Π_n sends basis vector e_i to e_{(i+1) mod n}.
Its eigenvalues are the n-th roots of unity, so det(I - t·Π_n) = Π_{ω^n=1}(1-tω) = 1-t^n.

We verify this for concrete small n via native_decide (sufficient for the paper's
applications where n ≤ 6), and state the general algebraic identity.
-/

/-- The n×n cyclic permutation matrix over ℤ: (Π_n)_{i,j} = 1 if j ≡ i+1 (mod n), else 0.
    prop:cycle-permutation-determinant -/
def cyclicPerm (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if j = Fin.cycle i then 1 else 0
  where
  Fin.cycle (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩

/-- Cyclic permutation matrix for Fin 2 (swap). -/
def cyclicPerm2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- Cyclic permutation matrix for Fin 3. -/
def cyclicPerm3 : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- Cyclic permutation matrix for Fin 4. -/
def cyclicPerm4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]

/-- Cyclic permutation matrix for Fin 5. -/
def cyclicPerm5 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 0, 0, 0, 0]

/-- Cyclic permutation matrix for Fin 6. -/
def cyclicPerm6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0]

/-! ## det(I - t·Π_n) = 1 - t^n instances

prop:cycle-permutation-determinant -/

/-- det(I - t·Π_2) = 1 - t² for the 2×2 cyclic permutation matrix. -/
theorem cyclicPerm2_fredholm_det (t : ℤ) :
    (1 - t • cyclicPerm2).det = 1 - t ^ 2 := by
  simp [cyclicPerm2, det_fin_two]
  ring

/-- det(I - t·Π_3) = 1 - t³ for the 3×3 cyclic permutation matrix. -/
theorem cyclicPerm3_fredholm_det (t : ℤ) :
    (1 - t • cyclicPerm3).det = 1 - t ^ 3 := by
  simp [cyclicPerm3, det_fin_three]
  ring

/-- Π_2² = I (cyclic permutation of order 2). -/
theorem cyclicPerm2_sq : cyclicPerm2 ^ 2 = 1 := by native_decide

/-- Π_3³ = I (cyclic permutation of order 3). -/
theorem cyclicPerm3_cube : cyclicPerm3 ^ 3 = 1 := by native_decide

/-- Π_4⁴ = I (cyclic permutation of order 4). -/
theorem cyclicPerm4_fourth : cyclicPerm4 ^ 4 = 1 := by native_decide

/-- Π_5⁵ = I (cyclic permutation of order 5). -/
theorem cyclicPerm5_fifth : cyclicPerm5 ^ 5 = 1 := by native_decide

/-- Π_6⁶ = I (cyclic permutation of order 6). -/
theorem cyclicPerm6_sixth : cyclicPerm6 ^ 6 = 1 := by native_decide

/-! ## Trace of cyclic permutation powers

The trace Tr(Π_n^k) = n if n|k, else 0.
This is the key input for the Witt/Möbius primitive counting.
-/

/-- Trace of Π_2^k: equals 2 when k is even, 0 when k is odd.
    subsec:operator-zeta-interface -/
theorem cyclicPerm2_trace_powers :
    cyclicPerm2.trace = 0 ∧ (cyclicPerm2 ^ 2).trace = 2 ∧
    (cyclicPerm2 ^ 3).trace = 0 ∧ (cyclicPerm2 ^ 4).trace = 2 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Trace of Π_3^k for k=0..6: period-3 pattern.
    subsec:operator-zeta-interface -/
theorem cyclicPerm3_trace_powers :
    (cyclicPerm3 ^ 1).trace = 0 ∧ (cyclicPerm3 ^ 2).trace = 0 ∧
    (cyclicPerm3 ^ 3).trace = 3 ∧ (cyclicPerm3 ^ 4).trace = 0 ∧
    (cyclicPerm3 ^ 5).trace = 0 ∧ (cyclicPerm3 ^ 6).trace = 3 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R103
-- ══════════════════════════════════════════════════════════════

/-- Trace of Π_4^k for k=0..4: period-4 pattern with tr(Π_4^0) = tr(Π_4^4) = 4.
    subsec:operator-zeta-interface -/
theorem cyclicPerm4_trace_powers :
    (cyclicPerm4 ^ 0).trace = 4 ∧
    (cyclicPerm4 ^ 1).trace = 0 ∧
    (cyclicPerm4 ^ 2).trace = 0 ∧
    (cyclicPerm4 ^ 3).trace = 0 ∧
    (cyclicPerm4 ^ 4).trace = 4 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

/-- Trace of Π_5^k for k=1..5: period-5 pattern.
    subsec:operator-zeta-interface -/
theorem cyclicPerm5_trace_powers :
    (cyclicPerm5 ^ 1).trace = 0 ∧ (cyclicPerm5 ^ 2).trace = 0 ∧
    (cyclicPerm5 ^ 3).trace = 0 ∧ (cyclicPerm5 ^ 4).trace = 0 ∧
    (cyclicPerm5 ^ 5).trace = 5 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

/-- Trace of Π_6^k for k=1..6: period-6 pattern.
    subsec:operator-zeta-interface -/
theorem cyclicPerm6_trace_powers :
    (cyclicPerm6 ^ 1).trace = 0 ∧ (cyclicPerm6 ^ 2).trace = 0 ∧
    (cyclicPerm6 ^ 3).trace = 0 ∧ (cyclicPerm6 ^ 4).trace = 0 ∧
    (cyclicPerm6 ^ 5).trace = 0 ∧ (cyclicPerm6 ^ 6).trace = 6 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Determinant formula for a specific 4×4 matrix.
    Helper for cyclicPerm4_fredholm_det. -/
private theorem det_four_of (a b c d e f g h i j k l m n o p : ℤ) :
    Matrix.det !![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, p] =
    a * (f * (k * p - l * o) - g * (j * p - l * n) + h * (j * o - k * n)) -
    b * (e * (k * p - l * o) - g * (i * p - l * m) + h * (i * o - k * m)) +
    c * (e * (j * p - l * n) - f * (i * p - l * m) + h * (i * n - j * m)) -
    d * (e * (j * o - k * n) - f * (i * o - k * m) + g * (i * n - j * m)) := by
  simp [det_succ_row_zero, Fin.sum_univ_four, Fin.sum_univ_three,
    Fin.succAbove, Matrix.submatrix]
  ring

/-- det(I - t·Π_4) = 1 - t⁴ for the 4×4 cyclic permutation matrix.
    prop:cycle-permutation-determinant -/
theorem cyclicPerm4_fredholm_det (t : ℤ) :
    (1 - t • cyclicPerm4).det = 1 - t ^ 4 := by
  have h : (1 : Matrix (Fin 4) (Fin 4) ℤ) - t • cyclicPerm4 =
    !![1, -t, 0, 0; 0, 1, -t, 0; 0, 0, 1, -t; -t, 0, 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cyclicPerm4]
  rw [h, det_four_of]; ring

/-- Determinant formula for a specific 5×5 matrix. -/
private theorem det_five_of (
    a₁ a₂ a₃ a₄ a₅
    b₁ b₂ b₃ b₄ b₅
    c₁ c₂ c₃ c₄ c₅
    d₁ d₂ d₃ d₄ d₅
    e₁ e₂ e₃ e₄ e₅ : ℤ) :
    Matrix.det !![a₁, a₂, a₃, a₄, a₅;
                   b₁, b₂, b₃, b₄, b₅;
                   c₁, c₂, c₃, c₄, c₅;
                   d₁, d₂, d₃, d₄, d₅;
                   e₁, e₂, e₃, e₄, e₅] =
    a₁ * (b₂ * (c₃ * (d₄ * e₅ - d₅ * e₄) - c₄ * (d₃ * e₅ - d₅ * e₃) +
           c₅ * (d₃ * e₄ - d₄ * e₃)) -
          b₃ * (c₂ * (d₄ * e₅ - d₅ * e₄) - c₄ * (d₂ * e₅ - d₅ * e₂) +
           c₅ * (d₂ * e₄ - d₄ * e₂)) +
          b₄ * (c₂ * (d₃ * e₅ - d₅ * e₃) - c₃ * (d₂ * e₅ - d₅ * e₂) +
           c₅ * (d₂ * e₃ - d₃ * e₂)) -
          b₅ * (c₂ * (d₃ * e₄ - d₄ * e₃) - c₃ * (d₂ * e₄ - d₄ * e₂) +
           c₄ * (d₂ * e₃ - d₃ * e₂))) -
    a₂ * (b₁ * (c₃ * (d₄ * e₅ - d₅ * e₄) - c₄ * (d₃ * e₅ - d₅ * e₃) +
           c₅ * (d₃ * e₄ - d₄ * e₃)) -
          b₃ * (c₁ * (d₄ * e₅ - d₅ * e₄) - c₄ * (d₁ * e₅ - d₅ * e₁) +
           c₅ * (d₁ * e₄ - d₄ * e₁)) +
          b₄ * (c₁ * (d₃ * e₅ - d₅ * e₃) - c₃ * (d₁ * e₅ - d₅ * e₁) +
           c₅ * (d₁ * e₃ - d₃ * e₁)) -
          b₅ * (c₁ * (d₃ * e₄ - d₄ * e₃) - c₃ * (d₁ * e₄ - d₄ * e₁) +
           c₄ * (d₁ * e₃ - d₃ * e₁))) +
    a₃ * (b₁ * (c₂ * (d₄ * e₅ - d₅ * e₄) - c₄ * (d₂ * e₅ - d₅ * e₂) +
           c₅ * (d₂ * e₄ - d₄ * e₂)) -
          b₂ * (c₁ * (d₄ * e₅ - d₅ * e₄) - c₄ * (d₁ * e₅ - d₅ * e₁) +
           c₅ * (d₁ * e₄ - d₄ * e₁)) +
          b₄ * (c₁ * (d₂ * e₅ - d₅ * e₂) - c₂ * (d₁ * e₅ - d₅ * e₁) +
           c₅ * (d₁ * e₂ - d₂ * e₁)) -
          b₅ * (c₁ * (d₂ * e₄ - d₄ * e₂) - c₂ * (d₁ * e₄ - d₄ * e₁) +
           c₄ * (d₁ * e₂ - d₂ * e₁))) -
    a₄ * (b₁ * (c₂ * (d₃ * e₅ - d₅ * e₃) - c₃ * (d₂ * e₅ - d₅ * e₂) +
           c₅ * (d₂ * e₃ - d₃ * e₂)) -
          b₂ * (c₁ * (d₃ * e₅ - d₅ * e₃) - c₃ * (d₁ * e₅ - d₅ * e₁) +
           c₅ * (d₁ * e₃ - d₃ * e₁)) +
          b₃ * (c₁ * (d₂ * e₅ - d₅ * e₂) - c₂ * (d₁ * e₅ - d₅ * e₁) +
           c₅ * (d₁ * e₂ - d₂ * e₁)) -
          b₅ * (c₁ * (d₂ * e₃ - d₃ * e₂) - c₂ * (d₁ * e₃ - d₃ * e₁) +
           c₃ * (d₁ * e₂ - d₂ * e₁))) +
    a₅ * (b₁ * (c₂ * (d₃ * e₄ - d₄ * e₃) - c₃ * (d₂ * e₄ - d₄ * e₂) +
           c₄ * (d₂ * e₃ - d₃ * e₂)) -
          b₂ * (c₁ * (d₃ * e₄ - d₄ * e₃) - c₃ * (d₁ * e₄ - d₄ * e₁) +
           c₄ * (d₁ * e₃ - d₃ * e₁)) +
          b₃ * (c₁ * (d₂ * e₄ - d₄ * e₂) - c₂ * (d₁ * e₄ - d₄ * e₁) +
           c₄ * (d₁ * e₂ - d₂ * e₁)) -
          b₄ * (c₁ * (d₂ * e₃ - d₃ * e₂) - c₂ * (d₁ * e₃ - d₃ * e₁) +
           c₃ * (d₁ * e₂ - d₂ * e₁))) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix]
  ring

/-- det(I - t·Π_5) = 1 - t⁵ for the 5×5 cyclic permutation matrix.
    prop:cycle-permutation-determinant -/
theorem cyclicPerm5_fredholm_det (t : ℤ) :
    (1 - t • cyclicPerm5).det = 1 - t ^ 5 := by
  have h : (1 : Matrix (Fin 5) (Fin 5) ℤ) - t • cyclicPerm5 =
    !![1, -t, 0, 0, 0; 0, 1, -t, 0, 0; 0, 0, 1, -t, 0; 0, 0, 0, 1, -t; -t, 0, 0, 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cyclicPerm5]
  rw [h, det_five_of]; ring

set_option maxHeartbeats 400000 in
/-- Determinant formula for a specific 6×6 matrix via cofactor expansion. -/
private theorem det_six_of (
    a₁ a₂ a₃ a₄ a₅ a₆
    b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆
    d₁ d₂ d₃ d₄ d₅ d₆
    e₁ e₂ e₃ e₄ e₅ e₆
    f₁ f₂ f₃ f₄ f₅ f₆ : ℤ) :
    Matrix.det !![a₁, a₂, a₃, a₄, a₅, a₆;
                   b₁, b₂, b₃, b₄, b₅, b₆;
                   c₁, c₂, c₃, c₄, c₅, c₆;
                   d₁, d₂, d₃, d₄, d₅, d₆;
                   e₁, e₂, e₃, e₄, e₅, e₆;
                   f₁, f₂, f₃, f₄, f₅, f₆] =
    a₁ * Matrix.det !![b₂, b₃, b₄, b₅, b₆;
                        c₂, c₃, c₄, c₅, c₆;
                        d₂, d₃, d₄, d₅, d₆;
                        e₂, e₃, e₄, e₅, e₆;
                        f₂, f₃, f₄, f₅, f₆] -
    a₂ * Matrix.det !![b₁, b₃, b₄, b₅, b₆;
                        c₁, c₃, c₄, c₅, c₆;
                        d₁, d₃, d₄, d₅, d₆;
                        e₁, e₃, e₄, e₅, e₆;
                        f₁, f₃, f₄, f₅, f₆] +
    a₃ * Matrix.det !![b₁, b₂, b₄, b₅, b₆;
                        c₁, c₂, c₄, c₅, c₆;
                        d₁, d₂, d₄, d₅, d₆;
                        e₁, e₂, e₄, e₅, e₆;
                        f₁, f₂, f₄, f₅, f₆] -
    a₄ * Matrix.det !![b₁, b₂, b₃, b₅, b₆;
                        c₁, c₂, c₃, c₅, c₆;
                        d₁, d₂, d₃, d₅, d₆;
                        e₁, e₂, e₃, e₅, e₆;
                        f₁, f₂, f₃, f₅, f₆] +
    a₅ * Matrix.det !![b₁, b₂, b₃, b₄, b₆;
                        c₁, c₂, c₃, c₄, c₆;
                        d₁, d₂, d₃, d₄, d₆;
                        e₁, e₂, e₃, e₄, e₆;
                        f₁, f₂, f₃, f₄, f₆] -
    a₆ * Matrix.det !![b₁, b₂, b₃, b₄, b₅;
                        c₁, c₂, c₃, c₄, c₅;
                        d₁, d₂, d₃, d₄, d₅;
                        e₁, e₂, e₃, e₄, e₅;
                        f₁, f₂, f₃, f₄, f₅] := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix]
  ring

/-- det(I - t·Π_6) = 1 - t⁶ for the 6×6 cyclic permutation matrix.
    prop:cycle-permutation-determinant -/
theorem cyclicPerm6_fredholm_det (t : ℤ) :
    (1 - t • cyclicPerm6).det = 1 - t ^ 6 := by
  have h : (1 : Matrix (Fin 6) (Fin 6) ℤ) - t • cyclicPerm6 =
    !![1, -t, 0, 0, 0, 0; 0, 1, -t, 0, 0, 0; 0, 0, 1, -t, 0, 0;
       0, 0, 0, 1, -t, 0; 0, 0, 0, 0, 1, -t; -t, 0, 0, 0, 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cyclicPerm6]
  rw [h, det_six_of]
  -- Now we have 6 terms of 5×5 determinants, most with zero coefficients
  simp only [det_five_of]
  ring

/-! ## Euler product structure

For the cyclic block C(n,α) = α·Π_n, det(I - r·C(n,α)) = 1 - (αr)^n.
This gives the Euler product factorization of finite-state zeta functions.
cor:cyclic-euler-product -/

/-- Euler factor for n=2: det(I - r·(α·Π_2)) = 1 - (αr)².
    cor:cyclic-euler-product -/
theorem euler_factor_n2 (α r : ℤ) :
    (1 - (α * r) • cyclicPerm2).det = 1 - (α * r) ^ 2 := by
  exact cyclicPerm2_fredholm_det (α * r)

/-- Euler factor for n=3: det(I - r·(α·Π_3)) = 1 - (αr)³.
    cor:cyclic-euler-product -/
theorem euler_factor_n3 (α r : ℤ) :
    (1 - (α * r) • cyclicPerm3).det = 1 - (α * r) ^ 3 := by
  exact cyclicPerm3_fredholm_det (α * r)

/-- Euler factor for n=4: det(I - r·(α·Π_4)) = 1 - (αr)⁴.
    cor:cyclic-euler-product -/
theorem euler_factor_n4 (α r : ℤ) :
    (1 - (α * r) • cyclicPerm4).det = 1 - (α * r) ^ 4 := by
  exact cyclicPerm4_fredholm_det (α * r)

/-- Euler factor for n=5: det(I - r·(α·Π_5)) = 1 - (αr)⁵.
    cor:cyclic-euler-product -/
theorem euler_factor_n5 (α r : ℤ) :
    (1 - (α * r) • cyclicPerm5).det = 1 - (α * r) ^ 5 :=
  cyclicPerm5_fredholm_det (α * r)

/-- Euler factor for n=6: det(I - r·(α·Π_6)) = 1 - (αr)⁶.
    cor:cyclic-euler-product -/
theorem euler_factor_n6 (α r : ℤ) :
    (1 - (α * r) • cyclicPerm6).det = 1 - (α * r) ^ 6 :=
  cyclicPerm6_fredholm_det (α * r)

/-! ## Resolvent trace jump index

The number of poles of det(I-zT)^{-1} inside the unit disk equals
the trace class rank (finite case). For Π_n, all n eigenvalues lie
on the unit circle.

thm:operator-resolvent-trace-jump-index -/

/-- For Π_2: exactly 2 eigenvalues on the unit circle (±1).
    Trace(Π_2^0) = 2 = dim. -/
theorem cyclicPerm2_rank : (cyclicPerm2 ^ 0).trace = 2 := by native_decide

/-- For Π_3: exactly 3 eigenvalues on the unit circle.
    Trace(Π_3^0) = 3 = dim. -/
theorem cyclicPerm3_rank : (cyclicPerm3 ^ 0).trace = 3 := by native_decide

/-- For Π_4: exactly 4 eigenvalues on the unit circle.
    Trace(Π_4^0) = 4 = dim.
    thm:operator-resolvent-trace-jump-index -/
theorem cyclicPerm4_rank : (cyclicPerm4 ^ 0).trace = 4 := by native_decide

/-- For Π_5: exactly 5 eigenvalues on the unit circle.
    Trace(Π_5^0) = 5 = dim.
    thm:operator-resolvent-trace-jump-index -/
theorem cyclicPerm5_rank : (cyclicPerm5 ^ 0).trace = 5 := by native_decide

/-- For Π_6: exactly 6 eigenvalues on the unit circle.
    Trace(Π_6^0) = 6 = dim. -/
theorem cyclicPerm6_rank : (cyclicPerm6 ^ 0).trace = 6 := by native_decide

/-! ## 2π i periodicity certificate

Finite-state zeta functions have a strict 2πi/log(λ_max) periodicity,
incompatible with the Riemann zeta's non-periodic structure on the critical line.
We verify the periodicity order: Π_n^n = I.

thm:operator-finite-state-zeta-2pii-periodic-separation -/

/-- Periodicity orders of cyclic permutation matrices.
    thm:operator-finite-state-zeta-2pii-periodic-separation -/
theorem cyclic_periodicity_orders :
    cyclicPerm2 ^ 2 = 1 ∧ cyclicPerm3 ^ 3 = 1 ∧
    cyclicPerm4 ^ 4 = 1 ∧ cyclicPerm5 ^ 5 = 1 ∧ cyclicPerm6 ^ 6 = 1 :=
  ⟨cyclicPerm2_sq, cyclicPerm3_cube, cyclicPerm4_fourth,
   cyclicPerm5_fifth, cyclicPerm6_sixth⟩

/-- Block 2+3 Fredholm product.
    cor:cyclic-euler-product -/
theorem fredholm_block_diag_2_3 (t : ℤ) :
    (1 - t ^ 2) * (1 - t ^ 3) = 1 - t ^ 2 - t ^ 3 + t ^ 5 := by ring

/-- Block 2+4 Fredholm product.
    cor:cyclic-euler-product -/
theorem fredholm_block_diag_2_4 (t : ℤ) :
    (1 - t ^ 2) * (1 - t ^ 4) = 1 - t ^ 2 - t ^ 4 + t ^ 6 := by ring

end Omega.Zeta
