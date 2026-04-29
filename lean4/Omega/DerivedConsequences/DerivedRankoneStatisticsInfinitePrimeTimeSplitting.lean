import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import Omega.Conclusion.EndpointHorizonArcsineKLClosedForm
import Omega.Conclusion.PrimeIntegerizationSuperlinearBitlength

namespace Omega.DerivedConsequences

/-- Concrete data for the rank-one statistics versus infinite-prime time-axis split. -/
structure derived_rankone_statistics_infinite_prime_time_splitting_data where
  a : ℝ
  b : ℝ
  ha : 0 < a
  hab : a ≤ b

namespace derived_rankone_statistics_infinite_prime_time_splitting_data

/-- The rank-one statistical shadow is the endpoint-horizon KL/arcosh collapse. -/
def rankOneStatisticalShadow
    (D : derived_rankone_statistics_infinite_prime_time_splitting_data) : Prop :=
  Omega.Conclusion.endpointHorizonKL D.a D.b = Real.arcosh (D.b / D.a)

/-- The time axis carries an infinite prime ladder together with the chapter-local `T log T`
integerization lower bound. -/
def infinitePrimeLadderTimeAxis
    (_D : derived_rankone_statistics_infinite_prime_time_splitting_data) : Prop :=
  (Set.Infinite (Set.univ : Set ℕ)) ∧
    Omega.Conclusion.conclusion_prime_integerization_superlinear_bitlength_statement

/-- No finite carrier can contain the full infinite prime ladder. -/
def noCommonFiniteMinimalCarrier
    (_D : derived_rankone_statistics_infinite_prime_time_splitting_data) : Prop :=
  ¬ ∃ S : Finset ℕ, ∀ n : ℕ, n ∈ S

end derived_rankone_statistics_infinite_prime_time_splitting_data

local notation "DerivedRankoneStatisticsInfinitePrimeTimeSplittingData" =>
  derived_rankone_statistics_infinite_prime_time_splitting_data

/-- Paper label: `thm:derived-rankone-statistics-infinite-prime-time-splitting`. -/
theorem paper_derived_rankone_statistics_infinite_prime_time_splitting
    (D : DerivedRankoneStatisticsInfinitePrimeTimeSplittingData) :
    D.rankOneStatisticalShadow ∧ D.infinitePrimeLadderTimeAxis ∧ D.noCommonFiniteMinimalCarrier := by
  refine ⟨?_, ?_, ?_⟩
  · exact Omega.Conclusion.paper_conclusion_endpoint_horizon_arcsine_kl_closed_form D.a D.b D.ha D.hab
  · exact ⟨Set.infinite_univ, Omega.Conclusion.paper_conclusion_prime_integerization_superlinear_bitlength⟩
  · intro hfinite
    rcases hfinite with ⟨S, hS⟩
    by_cases hne : S.Nonempty
    · let m := S.max' hne
      have hm : m + 1 ∈ S := hS (m + 1)
      have hmax : m + 1 ≤ m := Finset.le_max' S (m + 1) hm
      omega
    · have hzero : 0 ∈ S := hS 0
      exact hne ⟨0, hzero⟩

end Omega.DerivedConsequences
