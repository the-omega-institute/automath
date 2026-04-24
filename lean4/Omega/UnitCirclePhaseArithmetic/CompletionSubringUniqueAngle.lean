import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators
open Polynomial

/-- Evaluation of an integer polynomial at a rational point. -/
noncomputable def completionEval (P : Polynomial ℤ) (x : ℚ) : ℚ :=
  Polynomial.eval₂ (Int.castRingHom ℚ) x P

/-- The Chebyshev-style trace polynomial encoding `r^n + r^{-n}` as a polynomial in
`S = r + r^{-1}`. -/
noncomputable def completionTracePoly : ℕ → Polynomial ℤ
  | 0 => C 2
  | 1 => X
  | n + 2 => X * completionTracePoly (n + 1) - completionTracePoly n

private lemma mul_inv_pow_succ (r : ℚ) (n : ℕ) (hr : r ≠ 0) :
    r * r⁻¹ ^ (n + 1) = r⁻¹ ^ n := by
  calc
    r * r⁻¹ ^ (n + 1) = r * (r⁻¹ ^ n * r⁻¹) := by rw [pow_succ]
    _ = (r * r⁻¹) * r⁻¹ ^ n := by ring
    _ = r⁻¹ ^ n := by simp [hr]

private lemma inv_mul_pow_succ (r : ℚ) (n : ℕ) (hr : r ≠ 0) :
    r⁻¹ * r ^ (n + 1) = r ^ n := by
  calc
    r⁻¹ * r ^ (n + 1) = r⁻¹ * (r ^ n * r) := by rw [pow_succ]
    _ = (r⁻¹ * r) * r ^ n := by ring
    _ = r ^ n := by simp [hr]

private lemma completionTracePoly_eval (n : ℕ) (r : ℚ) (hr : r ≠ 0) :
    completionEval (completionTracePoly n) (r + r⁻¹) = r ^ n + r⁻¹ ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      norm_num [completionEval, completionTracePoly]
  | one =>
      simp [completionEval, completionTracePoly]
  | more n ih_n ih_n1 =>
      have ih_n' : Polynomial.eval₂ (Int.castRingHom ℚ) (r + r⁻¹) (completionTracePoly n) =
          r ^ n + r⁻¹ ^ n := by simpa [completionEval] using ih_n
      have ih_n1' :
          Polynomial.eval₂ (Int.castRingHom ℚ) (r + r⁻¹) (completionTracePoly (n + 1)) =
            r ^ (n + 1) + r⁻¹ ^ (n + 1) := by
              simpa [completionEval] using ih_n1
      rw [completionTracePoly, completionEval, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_X, ih_n1', ih_n']
      calc
        (r + r⁻¹) * (r ^ (n + 1) + r⁻¹ ^ (n + 1)) - (r ^ n + r⁻¹ ^ n)
            = r ^ (n + 2) + r * r⁻¹ ^ (n + 1) + (r⁻¹ * r ^ (n + 1) + r⁻¹ ^ (n + 2)) -
                (r ^ n + r⁻¹ ^ n) := by ring
        _ = r ^ (n + 2) + r⁻¹ ^ n + (r ^ n + r⁻¹ ^ (n + 2)) - (r ^ n + r⁻¹ ^ n) := by
              rw [mul_inv_pow_succ r n hr, inv_mul_pow_succ r n hr]
        _ = r ^ (n + 2) + r⁻¹ ^ (n + 2) := by ring

/-- The polynomial in `S = r + r⁻¹` obtained by pairing the Laurent coefficients of a symmetric
Laurent expression. -/
noncomputable def completionInvariantPoly (N : ℕ) (a : ℕ → ℤ) : Polynomial ℤ :=
  Finset.sum (Finset.range (N + 1)) fun k => C (a k) * completionTracePoly k

private lemma completionInvariantPoly_eval (N : ℕ) (a : ℕ → ℤ) (r : ℚ) (hr : r ≠ 0) :
    completionEval (completionInvariantPoly N a) (r + r⁻¹) =
      Finset.sum (Finset.range (N + 1)) (fun k => (a k : ℚ) * (r ^ k + r⁻¹ ^ k)) := by
  unfold completionInvariantPoly
  let s := Finset.range (N + 1)
  change completionEval (Finset.sum s fun k => C (a k) * completionTracePoly k) (r + r⁻¹) =
    Finset.sum s (fun k => (a k : ℚ) * (r ^ k + r⁻¹ ^ k))
  induction s using Finset.induction_on with
  | empty =>
      simp [completionEval]
  | @insert k s hk ih =>
      have htrace :
          Polynomial.eval₂ (Int.castRingHom ℚ) (r + r⁻¹) (completionTracePoly k) =
            r ^ k + (r ^ k)⁻¹ := by
              simpa [completionEval, inv_pow] using completionTracePoly_eval k r hr
      have hs :
          Polynomial.eval₂ (Int.castRingHom ℚ) (r + r⁻¹)
              (Finset.sum s fun x => (↑(a x) : Polynomial ℤ) * completionTracePoly x) =
            Finset.sum s (fun x => (a x : ℚ) * (r ^ x + (r ^ x)⁻¹)) := by
              simpa [completionEval, inv_pow] using ih
      have hcoeff :
          Polynomial.eval₂ (Int.castRingHom ℚ) (r + r⁻¹) ((↑(a k) : Polynomial ℤ)) = (a k : ℚ) := by
            change Polynomial.eval₂ (Int.castRingHom ℚ) (r + r⁻¹) (Polynomial.C (a k)) = (a k : ℚ)
            rw [eval₂_C]
            rfl
      simp [Finset.sum_insert, hk, completionEval]
      rw [htrace, hs]
      rw [hcoeff]

/-- Paper label: `prop:completion-subring-unique-angle`. -/
theorem paper_completion_subring_unique_angle (N : ℕ) (a : ℕ → ℤ) :
    ∃ P : Polynomial ℤ, ∀ r : ℚ, r ≠ 0 →
      completionEval P (r + r⁻¹) =
        Finset.sum (Finset.range (N + 1)) (fun k => (a k : ℚ) * (r ^ k + r⁻¹ ^ k)) := by
  refine ⟨completionInvariantPoly N a, ?_⟩
  intro r hr
  exact completionInvariantPoly_eval N a r hr

end Omega.UnitCirclePhaseArithmetic
