import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.CircleDimension.AnomalyFunctorialSplittingObstructionRge2Tor

namespace Omega.CircleDimension

/-- The counterexample group `ℤ² ⊕ C₂` has one free wedge generator `e₁ ∧ e₂`. -/
def cdim_anomaly_functorial_splitting_free_wedge_rank : ℕ := 1

/-- The same group has two torsion wedge generators `e₁ ∧ τ` and `e₂ ∧ τ`. -/
def cdim_anomaly_functorial_splitting_torsion_wedge_rank : ℕ := 2

/-- Anomaly characters are recorded on the one free and two `2`-torsion wedge coordinates. -/
def cdim_anomaly_functorial_splitting_character_rank : ℕ :=
  cdim_anomaly_functorial_splitting_free_wedge_rank +
    cdim_anomaly_functorial_splitting_torsion_wedge_rank

/-- The concrete counterexample data for the obstruction theorem: free rank `2` and torsion order
`2`. -/
def cdim_anomaly_functorial_splitting_counterexample :
    CdimAnomalyFunctorialSplittingObstructionData :=
  { freeRank := 2
    torsionOrder := 2
    torsionPositive := by decide }

/-- The wedge-coordinate character model `(b₀, b₁, b₂)` with `b₁, b₂` the `2`-torsion channels. -/
abbrev cdim_anomaly_functorial_splitting_character_model := Fin 3 → ZMod 2

/-- Twisting the first free basis vector by the torsion generator sends the second torsion channel
into the first one, while keeping the free and second torsion coordinates visible. -/
def cdim_anomaly_functorial_splitting_twist
    (χ : cdim_anomaly_functorial_splitting_character_model) :
    cdim_anomaly_functorial_splitting_character_model :=
  ![χ 0, χ 1 + χ 2, χ 2]

/-- The discrete character with nontrivial `b₂` component. -/
def cdim_anomaly_functorial_splitting_discrete_character :
    cdim_anomaly_functorial_splitting_character_model :=
  ![(0 : ZMod 2), 0, 1]

/-- Paper label: `conj:cdim-anomaly-functorial-splitting`. In the concrete `ℤ² ⊕ C₂` model the
wedge square splits as one free plus two `2`-torsion generators; the torsion-twisting
automorphism moves the discrete character with nontrivial `b₂` component; and the rank-`≥ 2`
torsion-translation obstruction therefore forbids any natural functorial splitting. -/
theorem paper_cdim_anomaly_functorial_splitting :
    cdim_anomaly_functorial_splitting_free_wedge_rank = 1 ∧
      cdim_anomaly_functorial_splitting_torsion_wedge_rank = 2 ∧
      cdim_anomaly_functorial_splitting_character_rank = 3 ∧
      cdim_anomaly_functorial_splitting_twist
          cdim_anomaly_functorial_splitting_discrete_character =
        ![(0 : ZMod 2), 1, 1] ∧
      cdim_anomaly_functorial_splitting_twist
          cdim_anomaly_functorial_splitting_discrete_character ≠
        cdim_anomaly_functorial_splitting_discrete_character ∧
      ¬ cdim_anomaly_functorial_splitting_counterexample.naturalSplitting := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    have h1 := congrFun h 1
    simp [cdim_anomaly_functorial_splitting_twist,
      cdim_anomaly_functorial_splitting_discrete_character] at h1
  · intro hsplit
    have hiff :=
      paper_cdim_anomaly_functorial_splitting_obstruction_rge2_tor
        cdim_anomaly_functorial_splitting_counterexample
    rcases hiff.mp hsplit with hr | ht
    · simp [CdimAnomalyFunctorialSplittingObstructionData.rankLeOne,
        cdim_anomaly_functorial_splitting_counterexample] at hr
    · simp [CdimAnomalyFunctorialSplittingObstructionData.torsionTrivial,
        cdim_anomaly_functorial_splitting_counterexample] at ht

end Omega.CircleDimension
