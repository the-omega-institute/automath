import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial
import Omega.POM.ToggleOrder

namespace Omega.POM

open Polynomial

/-- The substitution `t ↦ t²` used in the symmetric independent-set formulas. -/
noncomputable def symmetricIndsetSquareSubst : Polynomial ℤ :=
  X ^ 2

/-- The time-reversal-fixed independent-set polynomial of a path. The even and odd cases encode
the paper's split according to whether the central vertex is chosen. -/
noncomputable def pathTimeReversalSymmetricIndsetPoly (ℓ : Nat) : Polynomial ℤ :=
  if hEven : Even ℓ then
    (Omega.pathIndSetPoly (ℓ / 2 - 1)).comp symmetricIndsetSquareSubst
  else
    (Omega.pathIndSetPoly (ℓ / 2)).comp symmetricIndsetSquareSubst +
      X * (Omega.pathIndSetPoly (ℓ / 2 - 1)).comp symmetricIndsetSquareSubst

/-- The symmetric independent-set polynomial of a disjoint union of path components. -/
noncomputable def fiberTimeReversalSymmetricIndsetPolynomial : List Nat → Polynomial ℤ
  | [] => 1
  | ℓ :: lengths =>
      pathTimeReversalSymmetricIndsetPoly ℓ * fiberTimeReversalSymmetricIndsetPolynomial lengths

@[simp] theorem pathTimeReversalSymmetricIndsetPoly_even (n : Nat) :
    pathTimeReversalSymmetricIndsetPoly (2 * n) =
      (Omega.pathIndSetPoly (n - 1)).comp symmetricIndsetSquareSubst := by
  have hEven : Even (2 * n) := ⟨n, by ring⟩
  have hdiv : (2 * n) / 2 = n := by omega
  simp [pathTimeReversalSymmetricIndsetPoly, hEven, hdiv]

@[simp] theorem pathTimeReversalSymmetricIndsetPoly_odd (n : Nat) :
    pathTimeReversalSymmetricIndsetPoly (2 * n + 1) =
      (Omega.pathIndSetPoly n).comp symmetricIndsetSquareSubst +
        X * (Omega.pathIndSetPoly (n - 1)).comp symmetricIndsetSquareSubst := by
  have hOdd : ¬ Even (2 * n + 1) := by
    intro hEven
    rcases hEven with ⟨k, hk⟩
    omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [pathTimeReversalSymmetricIndsetPoly, hOdd, hdiv]

@[simp] theorem fiberTimeReversalSymmetricIndsetPolynomial_eq_prod (lengths : List Nat) :
    fiberTimeReversalSymmetricIndsetPolynomial lengths =
      (lengths.map pathTimeReversalSymmetricIndsetPoly).prod := by
  induction lengths with
  | nil =>
      rfl
  | cons ℓ lengths ih =>
      simp [fiberTimeReversalSymmetricIndsetPolynomial, ih]

/-- Paper-facing statement: the path formulas split by parity, and the fiberwise polynomial is the
product of the path contributions. -/
def TimeReversalSymmetricIndsetPolynomialStatement (lengths : List Nat) : Prop :=
  (∀ n : Nat,
    pathTimeReversalSymmetricIndsetPoly (2 * n) =
      (Omega.pathIndSetPoly (n - 1)).comp symmetricIndsetSquareSubst) ∧
  (∀ n : Nat,
    pathTimeReversalSymmetricIndsetPoly (2 * n + 1) =
      (Omega.pathIndSetPoly n).comp symmetricIndsetSquareSubst +
        X * (Omega.pathIndSetPoly (n - 1)).comp symmetricIndsetSquareSubst) ∧
  fiberTimeReversalSymmetricIndsetPolynomial lengths =
    (lengths.map pathTimeReversalSymmetricIndsetPoly).prod

/-- Paper wrapper: time-reversal-fixed independent-set polynomials on paths satisfy the even/odd
closed forms, and disjoint unions multiply over component lists. -/
theorem paper_pom_time_reversal_symmetric_indset_polynomial (lengths : List Nat) :
    TimeReversalSymmetricIndsetPolynomialStatement lengths := by
  exact ⟨pathTimeReversalSymmetricIndsetPoly_even, pathTimeReversalSymmetricIndsetPoly_odd,
    fiberTimeReversalSymmetricIndsetPolynomial_eq_prod lengths⟩

end Omega.POM
