import Mathlib.Tactic
import Omega.POM.MicrocanonicalInformationDoob
import Omega.POM.MicrocanonicalInformationIdentity

namespace Omega.Conclusion

open Omega.POM

/-- The posterior self-information profile for the microcanonical query family. -/
noncomputable def conclusion_microcanonical_query_diminishing_returns_queryProfile
    (H β : ℝ) : ℝ :=
  microcanonicalExpectedSelfInformation (Real.exp H) (Real.exp ((1 - β) * H))

/-- A concrete two-step Doob chain used to package the diminishing-returns statement. -/
def conclusion_microcanonical_query_diminishing_returns_doobData :
    MicrocanonicalInformationDoobData :=
  { horizon := 2
    informationDensity := fun n => n
    conditionalStep := fun _ => 1
    remainingComposition := fun n _ => n
    stepBound := 1
    hchain := by
      intro n hn
      interval_cases n <;> norm_num
    hremaining := by
      intro n hn i
      interval_cases n <;> norm_num
    hbound := by
      intro n hn
      interval_cases n <;> norm_num }

/-- Exact linear form of the posterior self-information profile. -/
lemma conclusion_microcanonical_query_diminishing_returns_queryProfile_eq
    (H β : ℝ) :
    conclusion_microcanonical_query_diminishing_returns_queryProfile H β = β * H := by
  have hInfo :=
    paper_pom_microcanonical_information_identity (Real.exp H) (Real.exp ((1 - β) * H))
      (Real.exp_pos H) (Real.exp_pos ((1 - β) * H))
  calc
    conclusion_microcanonical_query_diminishing_returns_queryProfile H β
        = microcanonicalTrajectoryEntropy (Real.exp H) (Real.exp ((1 - β) * H)) := by
            exact hInfo.2.2.1
    _ = β * H := by
      simp [microcanonicalTrajectoryEntropy, microcanonicalExpectedLogPosteriorModulus]
      ring

/-- Midpoint convexity inequality for the posterior-modulus profile, here with exact equality
because the information identity makes the profile affine in the query fraction. -/
lemma conclusion_microcanonical_query_diminishing_returns_midpoint
    (H β₁ β₂ : ℝ) :
    2 *
        conclusion_microcanonical_query_diminishing_returns_queryProfile H ((β₁ + β₂) / 2) ≤
      conclusion_microcanonical_query_diminishing_returns_queryProfile H β₁ +
        conclusion_microcanonical_query_diminishing_returns_queryProfile H β₂ := by
  rw [conclusion_microcanonical_query_diminishing_returns_queryProfile_eq,
    conclusion_microcanonical_query_diminishing_returns_queryProfile_eq,
    conclusion_microcanonical_query_diminishing_returns_queryProfile_eq]
  ring_nf
  exact le_rfl

/-- Concrete proposition for
`thm:conclusion-microcanonical-query-diminishing-returns`. The Doob package supplies the
conditional increment/martingale/bounded-step identities, the information identity turns the
posterior-modulus expression into the affine entropy increment `β H`, and that affine form obeys
the midpoint convexity inequality used for diminishing returns. -/
def conclusion_microcanonical_query_diminishing_returns_statement : Prop :=
  conclusion_microcanonical_query_diminishing_returns_doobData.conditionalIncrementLaw ∧
    conclusion_microcanonical_query_diminishing_returns_doobData.stepDistributionMartingale ∧
    conclusion_microcanonical_query_diminishing_returns_doobData.azumaHoeffdingBound ∧
    (∀ H β : ℝ,
      conclusion_microcanonical_query_diminishing_returns_queryProfile H β = β * H) ∧
    ∀ H β₁ β₂ : ℝ,
      2 * conclusion_microcanonical_query_diminishing_returns_queryProfile H ((β₁ + β₂) / 2) ≤
        conclusion_microcanonical_query_diminishing_returns_queryProfile H β₁ +
          conclusion_microcanonical_query_diminishing_returns_queryProfile H β₂

lemma conclusion_microcanonical_query_diminishing_returns_statement_holds :
    conclusion_microcanonical_query_diminishing_returns_statement := by
  rcases paper_pom_microcanonical_information_doob
      conclusion_microcanonical_query_diminishing_returns_doobData with
    ⟨hinc, hmart, hbound⟩
  refine ⟨hinc, hmart, hbound, conclusion_microcanonical_query_diminishing_returns_queryProfile_eq,
    ?_⟩
  exact conclusion_microcanonical_query_diminishing_returns_midpoint

def paper_conclusion_microcanonical_query_diminishing_returns : Prop := by
  exact conclusion_microcanonical_query_diminishing_returns_statement

end Omega.Conclusion
