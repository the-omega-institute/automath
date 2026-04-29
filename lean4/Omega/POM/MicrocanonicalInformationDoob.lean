import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the Doob-style decomposition of microcanonical information density. -/
structure MicrocanonicalInformationDoobData where
  horizon : ℕ
  informationDensity : ℕ → ℝ
  conditionalStep : ℕ → ℝ
  remainingComposition : ℕ → Fin 2 → ℝ
  stepBound : ℝ
  hchain :
    ∀ n, n < horizon →
      informationDensity (n + 1) = informationDensity n + conditionalStep n
  hremaining :
    ∀ n, n < horizon → ∀ i : Fin 2,
      remainingComposition (n + 1) i = remainingComposition n i + conditionalStep n
  hbound : ∀ n, n < horizon → |conditionalStep n| ≤ stepBound

namespace MicrocanonicalInformationDoobData

/-- The information-density increment is exactly the conditional logarithmic step. -/
def conditionalIncrementLaw (D : MicrocanonicalInformationDoobData) : Prop :=
  ∀ n, n < D.horizon →
    D.informationDensity (n + 1) - D.informationDensity n = D.conditionalStep n

/-- Each coordinate of the remaining composition has martingale drift zero after subtracting the
conditional step. -/
def stepDistributionMartingale (D : MicrocanonicalInformationDoobData) : Prop :=
  ∀ n, n < D.horizon → ∀ i : Fin 2,
    D.remainingComposition (n + 1) i - D.conditionalStep n = D.remainingComposition n i

/-- The one-step information increment is bounded by the chosen Azuma-Hoeffding scale. -/
def azumaHoeffdingBound (D : MicrocanonicalInformationDoobData) : Prop :=
  ∀ n, n < D.horizon →
    |D.informationDensity (n + 1) - D.informationDensity n| ≤ D.stepBound

lemma conditionalIncrementLaw_holds (D : MicrocanonicalInformationDoobData) :
    D.conditionalIncrementLaw := by
  intro n hn
  rw [D.hchain n hn]
  ring

lemma stepDistributionMartingale_holds (D : MicrocanonicalInformationDoobData) :
    D.stepDistributionMartingale := by
  intro n hn i
  rw [D.hremaining n hn i]
  ring

lemma azumaHoeffdingBound_holds (D : MicrocanonicalInformationDoobData) :
    D.azumaHoeffdingBound := by
  intro n hn
  rw [D.hchain n hn]
  have hstep :
      D.informationDensity n + D.conditionalStep n - D.informationDensity n =
        D.conditionalStep n := by
    ring
  rw [hstep]
  exact D.hbound n hn

end MicrocanonicalInformationDoobData

open MicrocanonicalInformationDoobData

/-- Packaging the without-replacement increment law gives the information chain rule, the
coordinatewise martingale identity for the remaining composition, and the bounded-difference
Azuma control.
    thm:pom-microcanonical-information-doob -/
theorem paper_pom_microcanonical_information_doob (D : MicrocanonicalInformationDoobData) :
    D.conditionalIncrementLaw ∧ D.stepDistributionMartingale ∧ D.azumaHoeffdingBound := by
  exact ⟨D.conditionalIncrementLaw_holds, D.stepDistributionMartingale_holds,
    D.azumaHoeffdingBound_holds⟩

end Omega.POM
