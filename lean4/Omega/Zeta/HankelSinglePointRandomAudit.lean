import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- The degree-`< 2d` audit polynomial extracted from the first `2d` values of a sequence. -/
noncomputable def hankelAuditPolynomial {k : Type*} [Field k] (d : ℕ) (a : ℕ → k) : k[X] := by
  classical
  exact Polynomial.ofFn (2 * d) (fun i : Fin (2 * d) => a i)

/-- If two degree-`< 2d` audit polynomials agree on more than `2d - 1` sample points, then their
first `2d` coefficients coincide. This packages the single-point audit principle in the
finite-window polynomial model underlying the Hankel collision bound.
    thm:xi-hankel-single-point-random-audit -/
theorem paper_xi_hankel_single_point_random_audit {k : Type*} [Field k]
    (d : ℕ) (a b : ℕ → k) (S : Finset k) :
    2 * d - 1 < S.card →
      (∀ r ∈ S, Polynomial.eval r (hankelAuditPolynomial d a) =
        Polynomial.eval r (hankelAuditPolynomial d b)) →
      ∀ n < 2 * d, a n = b n := by
  classical
  cases d with
  | zero =>
      intro _ _ n hn
      omega
  | succ d =>
      intro hcard hEval n hn
      have hdegA : (hankelAuditPolynomial (d + 1) a).natDegree < 2 * (d + 1) := by
        simpa [hankelAuditPolynomial] using
          (Polynomial.ofFn_natDegree_lt (R := k) (n := 2 * (d + 1))
            (by omega : 1 ≤ 2 * (d + 1)) (fun i : Fin (2 * (d + 1)) => a i))
      have hdegB : (hankelAuditPolynomial (d + 1) b).natDegree < 2 * (d + 1) := by
        simpa [hankelAuditPolynomial] using
          (Polynomial.ofFn_natDegree_lt (R := k) (n := 2 * (d + 1))
            (by omega : 1 ≤ 2 * (d + 1)) (fun i : Fin (2 * (d + 1)) => b i))
      have hmax :
          max (hankelAuditPolynomial (d + 1) a).natDegree
              (hankelAuditPolynomial (d + 1) b).natDegree < S.card := by
        refine max_lt_iff.mpr ?_
        constructor
        · exact lt_of_lt_of_le hdegA hcard
        · exact lt_of_lt_of_le hdegB hcard
      have hp :
          hankelAuditPolynomial (d + 1) a = hankelAuditPolynomial (d + 1) b :=
        Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
          (hankelAuditPolynomial (d + 1) a) (hankelAuditPolynomial (d + 1) b) S hEval hmax
      have hcoeff := congrArg (fun p : k[X] => p.coeff n) hp
      simpa [hankelAuditPolynomial, hn] using hcoeff

end Omega.Zeta
