import Mathlib.Tactic
import Omega.EA.Wedderburn
import Omega.Folding.RationalGeneratorGap

namespace Omega.EA

open scoped BigOperators

/-- The odd generators contributed by the `PU(d)` factor. The index `a : Fin (d - 1)` encodes the
class in degree `2(a+2)-1 = 2a+3`. -/
abbrev puOddGenerator (d : ℕ) := Fin (d - 1)

/-- The degree of the odd generator indexed by `a`. -/
def puOddGeneratorDegree {d : ℕ} (a : puOddGenerator d) : ℕ :=
  2 * a.1 + 3

/-- The product of the odd-degree `PU(d)` Poincare factors. -/
noncomputable def puFactorPoincarePolynomial (d : ℕ) : Polynomial ℤ :=
  ∏ a : puOddGenerator d, (Polynomial.X ^ puOddGeneratorDegree a + 1)

/-- Odd generators for the connected fold-groupoid automorphism product. -/
abbrev foldGroupoidAut0OddGenerator (m : ℕ) := Σ x : X m, puOddGenerator (X.fiberMultiplicity x)

/-- The finite-product Poincare polynomial obtained from the `PU(d_m(x))` factors. -/
noncomputable def foldGroupoidAut0PoincarePolynomial (m : ℕ) : Polynomial ℤ :=
  ∏ x : X m, puFactorPoincarePolynomial (X.fiberMultiplicity x)

lemma card_foldGroupoidAut0OddGenerator (m : ℕ) :
    Fintype.card (foldGroupoidAut0OddGenerator m) = ∑ x : X m, (X.fiberMultiplicity x - 1) := by
  classical
  simp [foldGroupoidAut0OddGenerator, puOddGenerator,
    Fintype.card_sigma (α := fun x : X m => Fin (X.fiberMultiplicity x - 1))]

/-- Paper label: `thm:fold-groupoid-aut0-rational-cohomology`. The connected fold-groupoid
automorphism proxy has the expected odd-degree generator count and the corresponding finite
product Poincare polynomial built from the `PU(d_m(x))` factors. -/
theorem paper_fold_groupoid_aut0_rational_cohomology (m : ℕ) :
    foldGroupoidAut0PoincarePolynomial m =
      ∏ x : X m, ∏ a : puOddGenerator (X.fiberMultiplicity x),
        (Polynomial.X ^ puOddGeneratorDegree a + 1) ∧
      Fintype.card (foldGroupoidAut0OddGenerator m) =
        ∑ x : X m, (X.fiberMultiplicity x - 1) ∧
      Fintype.card (foldGroupoidAut0OddGenerator m) =
        2 ^ m - (Finset.univ : Finset (X m)).card := by
  refine ⟨rfl, card_foldGroupoidAut0OddGenerator m, ?_⟩
  rw [card_foldGroupoidAut0OddGenerator]
  exact Omega.Folding.RationalGeneratorGap.paper_fold_groupoid_aut0_rational_generator_gap m

end Omega.EA
