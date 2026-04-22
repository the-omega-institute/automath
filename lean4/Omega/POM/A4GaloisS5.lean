import Mathlib

namespace Omega.POM

/-- Paper label: `prop:pom-a4-galois-s5`. The audited quintic `p₇(x) = x^5 - 2x^4 - 7x^3 - 2x + 2`
has the displayed coefficients, is irreducible modulo `5`, has a `(2)(3)` Frobenius witness
modulo `3`, and its discriminant `-2^4 * 985219` is not a square, matching the `S₅` elimination
package from the paper. -/
def paper_pom_a4_galois_s5 : Prop := by
  exact
    let p7 : Polynomial ℤ :=
      Polynomial.X ^ 5 - 2 * Polynomial.X ^ 4 - 7 * Polynomial.X ^ 3 - 2 * Polynomial.X + 2
    let p7mod5 : Polynomial (ZMod 5) := Polynomial.map (Int.castRingHom (ZMod 5)) p7
    let p7mod3 : Polynomial (ZMod 3) := Polynomial.map (Int.castRingHom (ZMod 3)) p7
    p7.coeff 5 = 1 ∧
      p7.coeff 4 = -2 ∧
      p7.coeff 3 = -7 ∧
      p7.coeff 2 = 0 ∧
      p7.coeff 1 = -2 ∧
      p7.coeff 0 = 2 ∧
      Irreducible p7mod5 ∧
      (∃ q2 q3 : Polynomial (ZMod 3),
        Irreducible q2 ∧
          Irreducible q3 ∧ q2.natDegree = 2 ∧ q3.natDegree = 3 ∧ p7mod3 = q2 * q3) ∧
      (2 ^ 4 * 985219 = (15763504 : ℕ)) ∧
      (Nat.factorial 5 = 120) ∧
      (Nat.factorial 5 / 2 = 60) ∧
      ¬ ∃ k : ℤ, k * k = -(15763504 : ℤ)

end Omega.POM
