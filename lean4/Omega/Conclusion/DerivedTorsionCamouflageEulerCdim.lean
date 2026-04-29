import Mathlib.Tactic
import Omega.Conclusion.CdimRankShortExactAdditivity
import Omega.CircleDimension.ShortExactAdditivity

namespace Omega.Conclusion

open Omega.CircleDimension

/-- Concrete three-term cohomology bookkeeping for the derived torsion-camouflage Euler package. -/
structure conclusion_derived_torsion_camouflage_euler_cdim_data where
  conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank : Nat
  conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank : Nat
  conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank : Nat
  conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard : Nat
  conclusion_derived_torsion_camouflage_euler_cdim_h1TorsionCard : Nat
  conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard : Nat

/-- Alternating Euler sum formed from the chapter-local circle-dimension bookkeeping. -/
def conclusion_derived_torsion_camouflage_euler_cdim_eulerCdim
    (D : conclusion_derived_torsion_camouflage_euler_cdim_data) : ℤ :=
  (circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank
      D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard : ℤ) -
    (circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank
        D.conclusion_derived_torsion_camouflage_euler_cdim_h1TorsionCard : ℤ) +
    (circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank
      D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard : ℤ)

/-- Alternating Euler sum on the rational ranks of the same three-term package. -/
def conclusion_derived_torsion_camouflage_euler_cdim_eulerRank
    (D : conclusion_derived_torsion_camouflage_euler_cdim_data) : ℤ :=
  (D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank : ℤ) -
    (D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank : ℤ) +
    (D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank : ℤ)

/-- Statement package for the derived torsion-camouflage Euler conclusion: each cohomology
circle-dimension is its rational rank, the alternating Euler sums agree, pure torsion contributes
zero, and direct sums remain additive. -/
def conclusion_derived_torsion_camouflage_euler_cdim_statement
    (D : conclusion_derived_torsion_camouflage_euler_cdim_data) : Prop :=
  (((circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank
          D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard : ℚ) =
        D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank) ∧
      ((circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank
            D.conclusion_derived_torsion_camouflage_euler_cdim_h1TorsionCard : ℚ) =
          D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank) ∧
      ((circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank
            D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard : ℚ) =
          D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank)) ∧
    conclusion_derived_torsion_camouflage_euler_cdim_eulerCdim D =
      conclusion_derived_torsion_camouflage_euler_cdim_eulerRank D ∧
    circleDim 0
        (D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard +
          D.conclusion_derived_torsion_camouflage_euler_cdim_h1TorsionCard +
          D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard) =
      0 ∧
    circleDim
        (D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank +
          D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank)
        (D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard +
          D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard) =
      circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank
          D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard +
        circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank
          D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard

/-- Paper label: `thm:conclusion-derived-torsion-camouflage-euler-cdim`. The bounded-complex
cohomology bookkeeping reduces every circle-dimension term to its free rank, so the Euler
alternating sum is unchanged; torsion-only terms vanish and the direct-sum clause is the usual
circle-dimension additivity. -/
theorem paper_conclusion_derived_torsion_camouflage_euler_cdim
    (D : conclusion_derived_torsion_camouflage_euler_cdim_data) :
    conclusion_derived_torsion_camouflage_euler_cdim_statement D := by
  have h0 :
      circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank
          D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard =
        D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank :=
    (Omega.CircleDimension.paper_killo_cdim_short_exact_additivity 0 0 0 0 0 0
      D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank
      D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard rfl).2.1
  have h1 :
      circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank
          D.conclusion_derived_torsion_camouflage_euler_cdim_h1TorsionCard =
        D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank :=
    (Omega.CircleDimension.paper_killo_cdim_short_exact_additivity 0 0 0 0 0 0
      D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank
      D.conclusion_derived_torsion_camouflage_euler_cdim_h1TorsionCard rfl).2.1
  have h2 :
      circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank
          D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard =
        D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank :=
    (Omega.CircleDimension.paper_killo_cdim_short_exact_additivity 0 0 0 0 0 0
      D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank
      D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard rfl).2.1
  have hsum :
      circleDim
          (D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank +
            D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank)
          (D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard +
            D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard) =
        circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank
            D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard +
          circleDim D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank
            D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard :=
    (paper_conclusion_cdim_rank_and_short_exact_additivity
      D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank
      (D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank +
        D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank)
      D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank
      D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard
      (D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard +
        D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard)
      D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard rfl).2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hsum⟩
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · simp [conclusion_derived_torsion_camouflage_euler_cdim_eulerCdim,
      conclusion_derived_torsion_camouflage_euler_cdim_eulerRank, h0, h1, h2]
  · simpa using circleDim_finite
      (D.conclusion_derived_torsion_camouflage_euler_cdim_h0TorsionCard +
        D.conclusion_derived_torsion_camouflage_euler_cdim_h1TorsionCard +
        D.conclusion_derived_torsion_camouflage_euler_cdim_h2TorsionCard)

end Omega.Conclusion
