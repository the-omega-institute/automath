import Mathlib.Tactic
import Omega.Zeta.XiExteriorPowerSmithSchubert

namespace Omega.Zeta

/-- Recursive helper producing the centered self-dual exponent pairs attached to a list of Smith
exponents. -/
def derived_schubert_smith_selfdual_moment_law_centeredPairListAux
    (q k : ℕ) : List ℕ → List ℤ
  | [] => []
  | e :: es =>
      let c : ℤ := (2 * e : ℤ) - (k * q : ℤ)
      c :: (-c) :: derived_schubert_smith_selfdual_moment_law_centeredPairListAux q k es

/-- The centered self-dual exponent pairs attached to the exterior-power Smith exponent multiset. -/
noncomputable def derived_schubert_smith_selfdual_moment_law_centeredPairList
    (q k : ℕ) : List ℤ :=
  derived_schubert_smith_selfdual_moment_law_centeredPairListAux q k
    (xiExteriorPowerSmithExponentMultiset q k).toList

/-- The quadratic moment of the centered self-dual exponent-pair model. -/
noncomputable def derived_schubert_smith_selfdual_moment_law_quadraticMoment
    (q k : ℕ) : ℤ :=
  ((derived_schubert_smith_selfdual_moment_law_centeredPairList q k).map fun z => z ^ 2).sum

private lemma derived_schubert_smith_selfdual_moment_law_centeredPairListAux_sum
    (q k : ℕ) (es : List ℕ) :
    (derived_schubert_smith_selfdual_moment_law_centeredPairListAux q k es).sum = 0 := by
  induction es with
  | nil =>
      simp [derived_schubert_smith_selfdual_moment_law_centeredPairListAux]
  | cons e es ih =>
      simp [derived_schubert_smith_selfdual_moment_law_centeredPairListAux, ih]

private lemma derived_schubert_smith_selfdual_moment_law_quadraticMomentAux
    (q k : ℕ) (es : List ℕ) :
    ((derived_schubert_smith_selfdual_moment_law_centeredPairListAux q k es).map fun z => z ^ 2).sum =
      2 * ((es.map fun e => (((2 * e : ℤ) - (k * q : ℤ)) ^ 2)).sum) := by
  induction es with
  | nil =>
      simp [derived_schubert_smith_selfdual_moment_law_centeredPairListAux]
  | cons e es ih =>
      simp [derived_schubert_smith_selfdual_moment_law_centeredPairListAux, ih, two_mul]
      ring

/-- Paper-facing self-dual moment package for the Schubert--Smith exponent list: the centered
pair model has zero total odd contribution at first order, and its quadratic moment is exactly the
doubled sum of the squared centered exponents.
    thm:derived-schubert-smith-selfdual-moment-law -/
theorem paper_derived_schubert_smith_selfdual_moment_law (q k : ℕ) :
    (derived_schubert_smith_selfdual_moment_law_centeredPairList q k).sum = 0 ∧
      derived_schubert_smith_selfdual_moment_law_quadraticMoment q k =
        2 * (((xiExteriorPowerSmithExponentMultiset q k).toList.map fun e =>
          (((2 * e : ℤ) - (k * q : ℤ)) ^ 2)).sum) := by
  constructor
  · unfold derived_schubert_smith_selfdual_moment_law_centeredPairList
    exact derived_schubert_smith_selfdual_moment_law_centeredPairListAux_sum q k _
  · unfold derived_schubert_smith_selfdual_moment_law_quadraticMoment
    unfold derived_schubert_smith_selfdual_moment_law_centeredPairList
    exact derived_schubert_smith_selfdual_moment_law_quadraticMomentAux q k _

end Omega.Zeta
