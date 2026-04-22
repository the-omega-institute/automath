import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local data for the functorial splitting obstruction on `ℤ^r ⊕ F`.
The finite torsion part is modeled by its order; the trivial torsion group has order `1`. -/
structure CdimAnomalyFunctorialSplittingObstructionData where
  freeRank : ℕ
  torsionOrder : ℕ
  torsionPositive : 1 ≤ torsionOrder

namespace CdimAnomalyFunctorialSplittingObstructionData

/-- The rank-`0/1` range where the wedge obstruction disappears. -/
def rankLeOne (D : CdimAnomalyFunctorialSplittingObstructionData) : Prop :=
  D.freeRank ≤ 1

/-- The torsion-free case, encoded by the trivial finite group of order `1`. -/
def torsionTrivial (D : CdimAnomalyFunctorialSplittingObstructionData) : Prop :=
  D.torsionOrder = 1

/-- The rank-`≥ 2` torsion twist acts on the connected anomaly circle by translation by `1`. -/
def twistTranslation (D : CdimAnomalyFunctorialSplittingObstructionData) :
    ZMod D.torsionOrder → ZMod D.torsionOrder :=
  fun x => x + 1

/-- A natural splitting is available either from the rank-`0/1` trivialization, from the
torsion-free trivialization, or from a fixed point for the twist translation on the connected
anomaly circle. -/
def naturalSplitting (D : CdimAnomalyFunctorialSplittingObstructionData) : Prop :=
  D.rankLeOne ∨ D.torsionTrivial ∨ ∃ x : ZMod D.torsionOrder, D.twistTranslation x = x

private theorem no_fixed_points_of_twist_translation (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ x : ZMod n, x + 1 = x := by
  intro h
  rcases h with ⟨x, hx⟩
  letI : Fact (1 < n) := ⟨lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  have h1 : (1 : ZMod n) = 0 := by
    exact add_left_cancel (a := x) (by simpa using hx)
  exact one_ne_zero h1

/-- Paper label: `thm:cdim-anomaly-functorial-splitting-obstruction-rge2-tor`.
In the chapter-local model, the only obstruction to a natural splitting is the presence of a
nontrivial torsion translation on the anomaly circle, which can occur only when the free rank is at
least `2` and the torsion factor is nontrivial. -/
theorem paper_cdim_anomaly_functorial_splitting_obstruction_rge2_tor
    (D : CdimAnomalyFunctorialSplittingObstructionData) :
    D.naturalSplitting ↔ D.rankLeOne ∨ D.torsionTrivial := by
  constructor
  · intro h
    rcases h with hr | ht | hfix
    · exact Or.inl hr
    · exact Or.inr ht
    · by_contra hgood
      rcases hfix with ⟨x, hx⟩
      have hnotTor : ¬ D.torsionTrivial := by
        intro ht
        exact hgood (Or.inr ht)
      have htor : 2 ≤ D.torsionOrder := by
        have hneq : 1 ≠ D.torsionOrder := by
          intro hEq
          apply hnotTor
          exact hEq.symm
        have hgt : 1 < D.torsionOrder := lt_of_le_of_ne D.torsionPositive hneq
        exact Nat.succ_le_of_lt hgt
      exact (no_fixed_points_of_twist_translation D.torsionOrder htor)
        ⟨x, by simpa [twistTranslation] using hx⟩
  · intro h
    exact h.elim Or.inl (fun ht => Or.inr (Or.inl ht))

end CdimAnomalyFunctorialSplittingObstructionData

open CdimAnomalyFunctorialSplittingObstructionData

theorem paper_cdim_anomaly_functorial_splitting_obstruction_rge2_tor
    (D : CdimAnomalyFunctorialSplittingObstructionData) :
    D.naturalSplitting ↔ D.rankLeOne ∨ D.torsionTrivial :=
  CdimAnomalyFunctorialSplittingObstructionData.paper_cdim_anomaly_functorial_splitting_obstruction_rge2_tor D

end Omega.CircleDimension
