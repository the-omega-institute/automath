import Mathlib.Tactic
import Omega.Folding.GaugePressureResolventDiscIdentity
import Omega.RootUnitCharacterPressureTensor.GaugePressureGenericGaloisS4

namespace Omega.RootUnitCharacterPressureTensor

/-- The sign cover is the audited hyperelliptic double cover cut out by the degree-`12`
branch polynomial `u (u - 1) P₁₀(u)`. -/
def gaugePressureSignCoverBranchDegree : ℕ := 12

/-- Hyperelliptic degree-`12` covers have genus `(12 - 2) / 2 = 5`. -/
def gaugePressureSignCoverGenus : ℕ := 5

/-- The unique index-`2` subgroup `A₄` has order `12`. -/
def gaugePressureAlternatingSubgroupOrder : ℕ := 12

/-- The corresponding quadratic subextension has degree `2`. -/
def gaugePressureQuadraticSubextensionDegree : ℕ :=
  Fintype.card (Equiv.Perm (Fin 4)) / gaugePressureAlternatingSubgroupOrder

/-- Paper-facing certificate for the sign-cover genus and quadratic subextension. -/
def gaugePressureSignCoverGenus5Statement : Prop :=
  (∀ u : ℚ,
    Omega.Folding.gaugePressureResolventDiscriminant u =
      -u * (u - 1) * Omega.Folding.gaugeAnomalyP10 u) ∧
    gaugePressureSignCoverBranchDegree = 12 ∧
    (gaugePressureSignCoverBranchDegree - 2) / 2 = gaugePressureSignCoverGenus ∧
    gaugePressureSignCoverGenus = 5 ∧
    gaugePressureAlternatingSubgroupOrder = 12 ∧
    gaugePressureQuadraticSubextensionDegree = 2 ∧
    ¬ IsSquare gaugePressureQuarticDiscriminantAtTwo

/-- Paper label: `thm:gauge-pressure-sign-cover-genus5`.
The discriminant branch polynomial is the squarefree degree-`12` sign cover input, the
hyperelliptic genus count gives `g = 5`, and the `S₄` certificate identifies the quadratic
subextension through the index-`2` subgroup `A₄`. -/
theorem paper_gauge_pressure_sign_cover_genus5 : gaugePressureSignCoverGenus5Statement := by
  have hS4 := paper_gauge_pressure_generic_galois_s4
  refine ⟨?_, rfl, by native_decide, rfl, rfl, ?_, hS4.2.2.2.2.1⟩
  · intro u
    simpa [Omega.Folding.GaugePressureResolventDiscIdentityData.p10Factorization] using
      (Omega.Folding.paper_root_unit_gauge_pressure_resolvent_disc_identity
        ({ u := u } : Omega.Folding.GaugePressureResolventDiscIdentityData)).2.2
  · unfold gaugePressureQuadraticSubextensionDegree gaugePressureAlternatingSubgroupOrder
    rw [hS4.2.2.2.2.2]

end Omega.RootUnitCharacterPressureTensor
