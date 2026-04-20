import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- The quintic characteristic polynomial `x^5 - 2 x^4 - t x^3 - 2 x + 2` over `ℤ`. -/
noncomputable def a4tCharpolyInt (t : ℤ) : Polynomial ℤ :=
  X ^ 5 - C (2 : ℤ) * X ^ 4 - C t * X ^ 3 - C (2 : ℤ) * X + C (2 : ℤ)

/-- The monic quadratic factor `x^2 + a x + b`. -/
noncomputable def a4tQuadraticFactor (a b : ℤ) : Polynomial ℤ :=
  X ^ 2 + C a * X + C b

/-- The monic cubic factor `x^3 + c x^2 + d x + e`. -/
noncomputable def a4tCubicFactor (c d e : ℤ) : Polynomial ℤ :=
  X ^ 3 + C c * X ^ 2 + C d * X + C e

/-- Integer-root branch of the rational-root test. -/
def A4TCharpolyHasIntegralRoot (t : ℤ) : Prop :=
  (a4tCharpolyInt t).eval (-2) = 0 ∨ (a4tCharpolyInt t).eval (-1) = 0 ∨
    (a4tCharpolyInt t).eval 1 = 0 ∨ (a4tCharpolyInt t).eval 2 = 0

/-- Concrete publication-facing content for the `A₄(t)` quintic: the rational-root branch occurs
exactly at `t = -1`, the surviving quadratic/cubic factorization is the explicit `t = 1` one, and
the `t = -1` specialization factors as the displayed linear-linear-cubic product. -/
def A4TCharpolyRationalReducibilityStatement (t : ℤ) : Prop :=
  (A4TCharpolyHasIntegralRoot t ↔ t = -1) ∧
    (a4tCharpolyInt t = a4tQuadraticFactor 0 1 * a4tCubicFactor (-2) (-2) 2 ↔ t = 1) ∧
    (t = -1 →
      a4tCharpolyInt t =
        (X - C (1 : ℤ)) * (X + C (1 : ℤ)) *
          (X ^ 3 - C (2 : ℤ) * X ^ 2 + C (2 : ℤ) * X - C (2 : ℤ)))

private lemma a4tCharpolyInt_eval_negTwo (t : ℤ) :
    (a4tCharpolyInt t).eval (-2) = 8 * t - 58 := by
  simp [a4tCharpolyInt]
  ring

private lemma a4tCharpolyInt_eval_negOne (t : ℤ) :
    (a4tCharpolyInt t).eval (-1) = t + 1 := by
  simp [a4tCharpolyInt]
  ring

private lemma a4tCharpolyInt_eval_one (t : ℤ) :
    (a4tCharpolyInt t).eval 1 = -t - 1 := by
  simp [a4tCharpolyInt]
  ring

private lemma a4tCharpolyInt_eval_two (t : ℤ) :
    (a4tCharpolyInt t).eval 2 = -(8 * t + 2) := by
  simp [a4tCharpolyInt]
  ring

private lemma a4tCharpolyInt_negOne_factor :
    a4tCharpolyInt (-1) =
      (X - C (1 : ℤ)) * (X + C (1 : ℤ)) * (X ^ 3 - C (2 : ℤ) * X ^ 2 + C (2 : ℤ) * X - C (2 : ℤ)) := by
  simp [a4tCharpolyInt]
  ring

private lemma a4tCharpolyInt_one_factor :
    a4tCharpolyInt 1 = a4tQuadraticFactor 0 1 * a4tCubicFactor (-2) (-2) 2 := by
  simp [a4tCharpolyInt, a4tQuadraticFactor, a4tCubicFactor]
  ring

private lemma a4tCharpolyInt_one_factor_only (t : ℤ)
    (hfac : a4tCharpolyInt t = a4tQuadraticFactor 0 1 * a4tCubicFactor (-2) (-2) 2) :
    t = 1 := by
  have hEval := congrArg (fun p : Polynomial ℤ => p.eval 1) hfac
  have hEval' :
      (a4tCharpolyInt t).eval 1 =
        (a4tQuadraticFactor 0 1 * a4tCubicFactor (-2) (-2) 2).eval 1 := by
    simpa using hEval
  rw [a4tCharpolyInt_eval_one] at hEval'
  simp [a4tQuadraticFactor, a4tCubicFactor] at hEval'
  omega

/-- The explicit linear-root branch lands only at `t = -1`, while the surviving quadratic/cubic
specialization is exactly the displayed factorization at `t = 1`.
    prop:pom-a4t-charpoly-rational-reducibility -/
theorem paper_pom_a4t_charpoly_rational_reducibility (t : ℤ) :
    A4TCharpolyRationalReducibilityStatement t := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hroot
      rcases hroot with hEval | hEval | hEval | hEval
      · rw [a4tCharpolyInt_eval_negTwo] at hEval
        omega
      · rw [a4tCharpolyInt_eval_negOne] at hEval
        omega
      · rw [a4tCharpolyInt_eval_one] at hEval
        omega
      · rw [a4tCharpolyInt_eval_two] at hEval
        omega
    · intro ht
      subst ht
      exact Or.inr (Or.inl (by rw [a4tCharpolyInt_eval_negOne]; norm_num))
  · constructor
    · exact a4tCharpolyInt_one_factor_only t
    · intro ht
      subst ht
      exact a4tCharpolyInt_one_factor
  · intro ht
    subst ht
    exact a4tCharpolyInt_negOne_factor

end Omega.POM
