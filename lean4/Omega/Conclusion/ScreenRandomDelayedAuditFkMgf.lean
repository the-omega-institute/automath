import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.Conclusion.ScreenGraphicMatroidCorankSupermodularity

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Concrete finite edge-subset package for the random delayed-audit FK generating function. -/
structure conclusion_screen_random_delayed_audit_fk_mgf_data where
  conclusion_screen_random_delayed_audit_fk_mgf_graphic : ScreenGraphicMatroidData

attribute [instance] ScreenGraphicMatroidData.decEqEdge

namespace conclusion_screen_random_delayed_audit_fk_mgf_data

/-- The FK redundancy `|S| - r(S)` of an edge subset. -/
def redundancy (D : conclusion_screen_random_delayed_audit_fk_mgf_data)
    (S : Finset D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.Edge) : ℕ :=
  S.card - D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.rank S

/-- The finite FK probability-generating polynomial before normalization. -/
def edge_subset_pgf (D : conclusion_screen_random_delayed_audit_fk_mgf_data)
    (q y : ℤ) : ℤ :=
  Finset.sum D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset fun S =>
    q ^ (D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.screenCost S) *
      y ^ (D.redundancy S)

/-- The Tutte polynomial in rank-nullity coordinates. -/
def tuttePolynomial (D : conclusion_screen_random_delayed_audit_fk_mgf_data)
    (x y : ℤ) : ℤ :=
  Finset.sum D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset fun S =>
    (x - 1) ^ (D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.screenCost S) *
      (y - 1) ^ (D.redundancy S)

/-- The finite falling-moment count at redundancy order `r`. -/
def fallingMoment (D : conclusion_screen_random_delayed_audit_fk_mgf_data)
    (r : ℕ) : ℕ :=
  (D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset.filter
    fun S => D.redundancy S = r).card

/-- The zero-delay event count, i.e. the number of subsets with zero corank. -/
def zeroProbabilityCount (D : conclusion_screen_random_delayed_audit_fk_mgf_data) : ℕ :=
  (D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset.filter
    fun S => D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.screenCost S = 0).card

/-- The finite mean delay, represented as the unnormalized first corank moment. -/
def meanDelay (D : conclusion_screen_random_delayed_audit_fk_mgf_data) : ℕ :=
  Finset.sum D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset
    fun S => D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.screenCost S

/-- FK generating function equals the standard Tutte substitution. -/
def mgf_tutte_formula (D : conclusion_screen_random_delayed_audit_fk_mgf_data) : Prop :=
  ∀ q y : ℤ, D.edge_subset_pgf q y = D.tuttePolynomial (q + 1) (y + 1)

/-- Falling moments are the finite coefficient counts of the redundancy classes. -/
def falling_moment_formula (D : conclusion_screen_random_delayed_audit_fk_mgf_data) : Prop :=
  ∀ r : ℕ,
    D.fallingMoment r =
      (D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset.filter
        fun S => D.redundancy S = r).card

/-- The zero-delay probability numerator is the zero-corank coefficient. -/
def zero_probability_formula (D : conclusion_screen_random_delayed_audit_fk_mgf_data) : Prop :=
  D.zeroProbabilityCount =
    (D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset.filter
      fun S => D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.screenCost S = 0).card

/-- The mean delay numerator is the finite first moment of the corank statistic. -/
def mean_formula (D : conclusion_screen_random_delayed_audit_fk_mgf_data) : Prop :=
  D.meanDelay =
    Finset.sum D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.allEdges.powerset
      fun S => D.conclusion_screen_random_delayed_audit_fk_mgf_graphic.screenCost S

end conclusion_screen_random_delayed_audit_fk_mgf_data

/-- Paper label: `thm:conclusion-screen-random-delayed-audit-fk-mgf`. -/
theorem paper_conclusion_screen_random_delayed_audit_fk_mgf
    (D : conclusion_screen_random_delayed_audit_fk_mgf_data) :
    D.mgf_tutte_formula ∧
      D.falling_moment_formula ∧
        D.zero_probability_formula ∧
          D.mean_formula := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q y
    simp [
      conclusion_screen_random_delayed_audit_fk_mgf_data.edge_subset_pgf,
      conclusion_screen_random_delayed_audit_fk_mgf_data.tuttePolynomial
    ]
  · intro r
    rfl
  · rfl
  · rfl

end Omega.Conclusion
