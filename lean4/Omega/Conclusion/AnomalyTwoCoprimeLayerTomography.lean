import Omega.Conclusion.CompleteStrictificationDualCriterion

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite basis-pairing data for two coprime lifted anomaly layers. The original
pairings are recorded on a chosen basis of `H₂(K; ℤ) / tors`, and the two lifts are modeled by the
corresponding `q₁`- and `q₂`-scaled pairings. -/
structure ConclusionAnomalyTwoCoprimeLayerTomographyData where
  β₂ : ℕ
  q₁ : ℕ
  q₂ : ℕ
  hq₁ : 2 ≤ q₁
  hq₂ : 2 ≤ q₂
  hcop : Nat.Coprime q₁ q₂
  basisPairing : Fin β₂ → ℕ

namespace ConclusionAnomalyTwoCoprimeLayerTomographyData

/-- The first coprime lifted pairing family. -/
def conclusion_anomaly_two_coprime_layer_tomography_firstLift
    (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) (j : Fin D.β₂) : ℕ :=
  D.q₁ * D.basisPairing j

/-- The second coprime lifted pairing family. -/
def conclusion_anomaly_two_coprime_layer_tomography_secondLift
    (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) (j : Fin D.β₂) : ℕ :=
  D.q₂ * D.basisPairing j

/-- Strictifiability is the vanishing of the original finite basis-pairing family. -/
def strictifiable (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) : Prop :=
  zeroVisibleAnomaly D.basisPairing

/-- The two coprime lifted layers both vanish on the chosen basis. -/
def twoCoprimeLayerVanishing (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) : Prop :=
  zeroVisibleAnomaly D.conclusion_anomaly_two_coprime_layer_tomography_firstLift ∧
    zeroVisibleAnomaly D.conclusion_anomaly_two_coprime_layer_tomography_secondLift

lemma conclusion_anomaly_two_coprime_layer_tomography_firstLift_zero_iff
    (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) :
    zeroVisibleAnomaly D.conclusion_anomaly_two_coprime_layer_tomography_firstLift ↔
      ∀ j, D.basisPairing j = 0 := by
  unfold zeroVisibleAnomaly
  rw [zero_sum_nat_iff_forall_zero]
  constructor
  · intro h j
    have hj : D.q₁ * D.basisPairing j = 0 := h j
    rcases Nat.mul_eq_zero.mp hj with hq₁ | hpair
    · have hq₁_pos : 0 < D.q₁ := lt_of_lt_of_le (by decide : 0 < 2) D.hq₁
      exact (False.elim <| Nat.ne_of_gt hq₁_pos hq₁)
    · exact hpair
  · intro h j
    simp [conclusion_anomaly_two_coprime_layer_tomography_firstLift, h j]

lemma conclusion_anomaly_two_coprime_layer_tomography_secondLift_zero_iff
    (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) :
    zeroVisibleAnomaly D.conclusion_anomaly_two_coprime_layer_tomography_secondLift ↔
      ∀ j, D.basisPairing j = 0 := by
  unfold zeroVisibleAnomaly
  rw [zero_sum_nat_iff_forall_zero]
  constructor
  · intro h j
    have hj : D.q₂ * D.basisPairing j = 0 := h j
    rcases Nat.mul_eq_zero.mp hj with hq₂ | hpair
    · have hq₂_pos : 0 < D.q₂ := lt_of_lt_of_le (by decide : 0 < 2) D.hq₂
      exact (False.elim <| Nat.ne_of_gt hq₂_pos hq₂)
    · exact hpair
  · intro h j
    simp [conclusion_anomaly_two_coprime_layer_tomography_secondLift, h j]

lemma conclusion_anomaly_two_coprime_layer_tomography_two_point_test
    (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) :
    D.strictifiable ↔ ∀ j, D.basisPairing j = 0 := by
  unfold strictifiable zeroVisibleAnomaly
  rw [zero_sum_nat_iff_forall_zero]

lemma conclusion_anomaly_two_coprime_layer_tomography_all_moments_collapse_to_two
    (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) :
    D.twoCoprimeLayerVanishing ↔ ∀ j, D.basisPairing j = 0 := by
  constructor
  · rintro ⟨h₁, _h₂⟩
    exact D.conclusion_anomaly_two_coprime_layer_tomography_firstLift_zero_iff.mp h₁
  · intro h
    refine ⟨?_, ?_⟩
    · exact D.conclusion_anomaly_two_coprime_layer_tomography_firstLift_zero_iff.mpr h
    · exact D.conclusion_anomaly_two_coprime_layer_tomography_secondLift_zero_iff.mpr h

end ConclusionAnomalyTwoCoprimeLayerTomographyData

/-- Paper label: `cor:conclusion-anomaly-two-coprime-layer-tomography`. For the concrete basis
pairings recorded in `D`, vanishing of the original anomaly class is equivalent to vanishing of
its two coprime lifted pairing families. -/
theorem paper_conclusion_anomaly_two_coprime_layer_tomography
    (D : ConclusionAnomalyTwoCoprimeLayerTomographyData) :
    D.strictifiable ↔ D.twoCoprimeLayerVanishing := by
  rw [D.conclusion_anomaly_two_coprime_layer_tomography_two_point_test,
    D.conclusion_anomaly_two_coprime_layer_tomography_all_moments_collapse_to_two]

end Omega.Conclusion
