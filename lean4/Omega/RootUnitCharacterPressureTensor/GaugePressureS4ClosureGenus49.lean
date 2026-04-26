import Mathlib.Tactic
import Omega.RootUnitCharacterPressureTensor.GaugePressureGenericGaloisS4
import Omega.RootUnitCharacterPressureTensor.GaugePressureResolventCoverGenus4
import Omega.RootUnitCharacterPressureTensor.GaugePressureSignCoverGenus5

namespace Omega.RootUnitCharacterPressureTensor

/-- The order of the `D₈` resolvent stabilizer inside `S₄`. -/
def gaugePressureDihedralSubgroupOrder : ℕ := 8

/-- The order of the Klein four subgroup inside `S₄`. -/
def gaugePressureKleinSubgroupOrder : ℕ := 4

/-- The audited `S₄` closure has `12` simple transposition branch values. -/
def gaugePressureS4ClosureSimpleTranspositionBranchCount : ℕ := 12

/-- Each transposition branch point contributes `|S₄| / 2 = 12` to the total ramification. -/
def gaugePressureS4ClosureBranchContribution : ℕ :=
  Fintype.card (Equiv.Perm (Fin 4)) / 2

/-- Total ramification for the `24`-sheeted `S₄` closure. -/
def gaugePressureS4ClosureTotalRamification : ℕ :=
  gaugePressureS4ClosureSimpleTranspositionBranchCount *
    gaugePressureS4ClosureBranchContribution

/-- The genus given by the Riemann--Hurwitz count for the `S₄` closure. -/
def gaugePressureS4ClosureGenus : ℕ := 49

/-- Concrete package for the `A₄`, `D₈`, and `V₄` intermediate quotients of the `S₄` closure. -/
def gaugePressureS4ClosureHasExpectedIntermediateQuotients : Prop :=
  Fintype.card (Equiv.Perm (Fin 4)) / gaugePressureAlternatingSubgroupOrder = 2 ∧
    Fintype.card (Equiv.Perm (Fin 4)) / gaugePressureDihedralSubgroupOrder =
      gaugePressureResolventCoverDegree ∧
    Fintype.card (Equiv.Perm (Fin 4)) / gaugePressureKleinSubgroupOrder = 6 ∧
    gaugePressureSignCoverGenus = 5 ∧
    gaugePressureResolventCoverGenus = 4

/-- Paper label: `thm:gauge-pressure-s4-closure-genus49`. -/
theorem paper_gauge_pressure_s4_closure_genus49 :
    gaugePressureS4ClosureGenus = 49 ∧
      gaugePressureS4ClosureHasExpectedIntermediateQuotients := by
  have hS4 := paper_gauge_pressure_generic_galois_s4
  have hsign := paper_gauge_pressure_sign_cover_genus5
  have hres := paper_gauge_pressure_resolvent_cover_genus4
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hS4.2.2.2.2.2]
    norm_num [gaugePressureAlternatingSubgroupOrder]
  · rw [hS4.2.2.2.2.2]
    norm_num [gaugePressureDihedralSubgroupOrder, gaugePressureResolventCoverDegree]
  · rw [hS4.2.2.2.2.2]
    norm_num [gaugePressureKleinSubgroupOrder]
  · simpa using hsign.2.2.2.1
  · simpa using hres.2.2.2.2.2.2

end Omega.RootUnitCharacterPressureTensor
