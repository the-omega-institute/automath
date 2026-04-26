import Mathlib.Tactic

namespace Omega.Zeta

/-- The only two intersection classes allowed by the `S10` shadow certificate. -/
inductive xi_time_part75_p10_shadow_universal_ramification_shielding_intersection
  | rational
  | quadratic

/-- Concrete `S10` splitting-field and ramification-disjointness certificate. -/
structure xi_time_part75_p10_shadow_universal_ramification_shielding_data where
  s10SplittingFieldDegree : ℕ
  auxiliaryFieldDegree : ℕ
  compositumDegree : ℕ
  uniqueQuadraticDiscriminant : ℤ
  splittingRamifiedPrimes : Finset ℕ
  auxiliaryRamifiedPrimes : Finset ℕ
  intersectionCandidate :
    xi_time_part75_p10_shadow_universal_ramification_shielding_intersection
  s10DegreeCertificate : s10SplittingFieldDegree = 3628800
  uniqueQuadraticSubfieldCertificate : uniqueQuadraticDiscriminant ≠ 0
  intersectionClassification :
    intersectionCandidate =
        xi_time_part75_p10_shadow_universal_ramification_shielding_intersection.rational ∨
      intersectionCandidate =
        xi_time_part75_p10_shadow_universal_ramification_shielding_intersection.quadratic
  quadraticIntersectionRamifies :
    intersectionCandidate =
        xi_time_part75_p10_shadow_universal_ramification_shielding_intersection.quadratic →
      ∃ p, p ∈ splittingRamifiedPrimes ∧ p ∈ auxiliaryRamifiedPrimes
  ramificationDisjoint :
    ∀ p, p ∈ splittingRamifiedPrimes → p ∈ auxiliaryRamifiedPrimes → False
  compositumDegreeCertificate :
    compositumDegree = s10SplittingFieldDegree * auxiliaryFieldDegree

namespace xi_time_part75_p10_shadow_universal_ramification_shielding_data

/-- The Galois intersection is trivial. -/
def intersectionTrivial
    (D : xi_time_part75_p10_shadow_universal_ramification_shielding_data) : Prop :=
  D.intersectionCandidate =
    xi_time_part75_p10_shadow_universal_ramification_shielding_intersection.rational

/-- With trivial intersection, the compositum degree is the product degree. -/
def linearDisjointProduct
    (D : xi_time_part75_p10_shadow_universal_ramification_shielding_data) : Prop :=
  D.intersectionTrivial ∧
    D.compositumDegree = D.s10SplittingFieldDegree * D.auxiliaryFieldDegree ∧
    D.s10SplittingFieldDegree = 3628800

end xi_time_part75_p10_shadow_universal_ramification_shielding_data

/-- Paper label: `thm:xi-time-part75-p10-shadow-universal-ramification-shielding`. The `S10`
certificate leaves only the rational field and the unique quadratic subfield as possible
intersections. The quadratic case would force common ramification, contradicting the disjoint
ramification ledger, so the intersection is trivial and the product degree follows. -/
theorem paper_xi_time_part75_p10_shadow_universal_ramification_shielding
    (D : xi_time_part75_p10_shadow_universal_ramification_shielding_data) :
    D.intersectionTrivial ∧ D.linearDisjointProduct := by
  have hnot_quadratic :
      D.intersectionCandidate ≠
        xi_time_part75_p10_shadow_universal_ramification_shielding_intersection.quadratic := by
    intro hquadratic
    rcases D.quadraticIntersectionRamifies hquadratic with ⟨p, hp_split, hp_aux⟩
    exact D.ramificationDisjoint p hp_split hp_aux
  have htrivial : D.intersectionTrivial := by
    rcases D.intersectionClassification with hrational | hquadratic
    · exact hrational
    · exact False.elim (hnot_quadratic hquadratic)
  exact ⟨htrivial, htrivial, D.compositumDegreeCertificate, D.s10DegreeCertificate⟩

end Omega.Zeta
