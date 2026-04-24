import Mathlib.Tactic
import Omega.GU.Window6DyadicBudget
import Omega.GroupUnification.PatiSalamGlobalFormRigidity
import Omega.GroupUnification.TerminalWindow6OneEightTwelveSplit

namespace Omega.GroupUnification

/-- The audited Pati-Salam rigidity witness used in the common-refinement argument. -/
def window6CommonRefinementPatiSalamData : PatiSalamGlobalFormRigidityData where
  kernelCard := 1
  lostTwoTorsionClasses := 0
  nontrivialKernelRemovesTwoTorsion := by
    intro h
    exfalso
    exact h rfl
  boundaryRankThreeInjection := by
    dsimp [patiSalamUniversalCenterTwoRank]
    omega

/-- The Pati-Salam adjoint dimension `15 + 3 + 3`. -/
def window6PatiSalamAdjointDim : ℕ := 15 + 3 + 3

/-- The audited terminal split `1 + 8 + 12`. -/
def window6TerminalRefinementDim : ℕ := 1 + 8 + 12

/-- The explicit `1 ⊕ 8 ⊕ 12` terminal split proposition. -/
def window6TerminalSplitAudit : Prop :=
  window6ZeroSector.card = 1 ∧
    window6LightSector.card = 8 ∧
    window6HeavySector.card = 12 ∧
    Disjoint window6ZeroSector window6LightSector ∧
    Disjoint window6ZeroSector window6HeavySector ∧
    Disjoint window6LightSector window6HeavySector ∧
    window6ZeroSector ∪ window6LightSector ∪ window6HeavySector = Finset.univ

/-- The closed light sector inside the `su(4)` adjoint block. -/
def window6LightSectorLeviDim : ℕ := 1 + 8

/-- The Standard-Model Levi dimensions `su(3) ⊕ u(1) ⊕ su(2)_L ⊕ su(2)_R`. -/
def window6SMLeviDim : ℕ := 8 + 1 + 3 + 3

/-- The audited decompositions `21 = 15 + 3 + 3` and `21 = 1 + 8 + 12`, together with the
Pati-Salam global-form wrapper, force the `su(4) ⊕ su(2)_L ⊕ su(2)_R` skeleton; the closed
`1 ⊕ 8` light sector inside the `15`-block isolates the Standard-Model Levi dimensions
`8 + 1 + 3 + 3`.
    prop:window6-common-refinement-sm-levi -/
theorem paper_window6_common_refinement_sm_levi :
    window6TerminalSplitAudit ∧
      window6PatiSalamAdjointDim = 21 ∧
      window6TerminalRefinementDim = 21 ∧
      window6CommonRefinementPatiSalamData.globalFormIsSU4xSU2xSU2 ∧
      window6LightSectorLeviDim = 9 ∧
      15 = window6LightSectorLeviDim + 6 ∧
      window6SMLeviDim = 15 := by
  have hbudget := Omega.GU.Window6DyadicBudget.paper_gut_window6_dyadic_budget_three_stage
  have hps :
      window6CommonRefinementPatiSalamData.globalFormIsSU4xSU2xSU2 :=
    paper_window6_levi_rigidity_pati_salam_isogeny window6CommonRefinementPatiSalamData
  refine ⟨paper_terminal_window6_1_8_12_split, ?_, ?_, hps, ?_, ?_, ?_⟩
  · calc
      window6PatiSalamAdjointDim = Nat.fib 8 := by
        simpa [window6PatiSalamAdjointDim] using hbudget.2.2.2.2.2.2.2.1
      _ = 21 := hbudget.2.1
  · norm_num [window6TerminalRefinementDim]
  · norm_num [window6LightSectorLeviDim]
  · norm_num [window6LightSectorLeviDim]
  · norm_num [window6SMLeviDim]

/-- Paper-facing residual Standard-Model package extracted from the common-refinement audit.
    cor:window6-levi-rigidity-sm-residual -/
theorem paper_window6_levi_rigidity_sm_residual :
    window6CommonRefinementPatiSalamData.globalFormIsSU4xSU2xSU2 ∧
      window6LightSectorLeviDim = 9 ∧
      window6SMLeviDim = 15 := by
  rcases paper_window6_common_refinement_sm_levi with
    ⟨_, _, _, hglobal, hlight, _, hsm⟩
  exact ⟨hglobal, hlight, hsm⟩

end Omega.GroupUnification
