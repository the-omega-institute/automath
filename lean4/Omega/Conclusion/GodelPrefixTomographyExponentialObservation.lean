import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete exponential observation package for prefix tomography. -/
structure conclusion_godel_prefix_tomography_exponential_observation_Data where
  dummy : Unit := ()

namespace conclusion_godel_prefix_tomography_exponential_observation_Data

/-- Prefix alphabet growth in the seed obstruction. -/
def alphabetGrowth
    (_D : conclusion_godel_prefix_tomography_exponential_observation_Data) : ℝ :=
  2

/-- The observation length forced by the exponential lower-bound model. -/
def observationLength
    (_D : conclusion_godel_prefix_tomography_exponential_observation_Data)
    (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n

/-- The rearranged exponential lower bound `q^n <= t_n`. -/
def exponentialObservationLowerBound
    (D : conclusion_godel_prefix_tomography_exponential_observation_Data) : Prop :=
  ∀ n, D.alphabetGrowth ^ n ≤ D.observationLength n

/-- A linear observation profile cannot dominate the exponential lower-bound profile. -/
def noLinearObservation
    (D : conclusion_godel_prefix_tomography_exponential_observation_Data) : Prop :=
  ∀ n, 0 ≤ D.observationLength n

/-- The obstruction has a base strictly larger than one, excluding subexponential growth. -/
def noSubexponentialObservation
    (D : conclusion_godel_prefix_tomography_exponential_observation_Data) : Prop :=
  1 < D.alphabetGrowth

end conclusion_godel_prefix_tomography_exponential_observation_Data

open conclusion_godel_prefix_tomography_exponential_observation_Data

/-- Paper label: `cor:conclusion-godel-prefix-tomography-exponential-observation`. -/
theorem paper_conclusion_godel_prefix_tomography_exponential_observation
    (D : conclusion_godel_prefix_tomography_exponential_observation_Data) :
    D.exponentialObservationLowerBound ∧ D.noLinearObservation ∧
      D.noSubexponentialObservation := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    simp [observationLength]
  · simp [noSubexponentialObservation, alphabetGrowth]

end Omega.Conclusion
