import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local data for the rank-`2` full-torsion translation on the connected anomaly circle.
The cyclic torsion factor has order `n ≥ 2`. -/
structure CdimAnomalyRank2FullTorsionTranslationData where
  torsionOrder : ℕ
  torsionOrder_ge_two : 2 ≤ torsionOrder

namespace CdimAnomalyRank2FullTorsionTranslationData

/-- Translation by the torsion generator on the connected anomaly circle `ℤ/nℤ`. -/
def torsionTranslation (D : CdimAnomalyRank2FullTorsionTranslationData) :
    ZMod D.torsionOrder → ZMod D.torsionOrder :=
  fun x => x + 1

/-- The `1/n`-translation acts transitively on the full `n`-torsion orbit. -/
def fullNTorsionTranslation (D : CdimAnomalyRank2FullTorsionTranslationData) : Prop :=
  Function.Surjective D.torsionTranslation

/-- No point of the anomaly circle is fixed by the torsion translation when `n ≥ 2`. -/
def noInvariantSection (D : CdimAnomalyRank2FullTorsionTranslationData) : Prop :=
  ¬ ∃ x : ZMod D.torsionOrder, D.torsionTranslation x = x

/-- Paper label: `cor:cdim-anomaly-rank2-full-torsion-translation`.
Translation by the torsion generator is surjective on the `n`-torsion anomaly circle, and for
`n ≥ 2` it has no fixed point, so no invariant section can exist. -/
theorem paper_cdim_anomaly_rank2_full_torsion_translation
    (D : CdimAnomalyRank2FullTorsionTranslationData) :
    D.fullNTorsionTranslation ∧ D.noInvariantSection := by
  refine ⟨?_, ?_⟩
  · intro x
    refine ⟨x - 1, by simp [torsionTranslation]⟩
  · intro h
    rcases h with ⟨x, hx⟩
    letI : Fact (1 < D.torsionOrder) := ⟨lt_of_lt_of_le (by decide : 1 < 2) D.torsionOrder_ge_two⟩
    have h1 : (1 : ZMod D.torsionOrder) = 0 := by
      exact add_left_cancel (a := x) (by simpa [torsionTranslation] using hx)
    exact one_ne_zero h1

end CdimAnomalyRank2FullTorsionTranslationData

open CdimAnomalyRank2FullTorsionTranslationData

theorem paper_cdim_anomaly_rank2_full_torsion_translation
    (D : CdimAnomalyRank2FullTorsionTranslationData) :
    D.fullNTorsionTranslation ∧ D.noInvariantSection :=
  CdimAnomalyRank2FullTorsionTranslationData.paper_cdim_anomaly_rank2_full_torsion_translation D

end Omega.CircleDimension
