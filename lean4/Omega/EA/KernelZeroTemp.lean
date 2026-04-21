import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.CarryZeroTempSupportCollapse

namespace Omega.EA

open scoped BigOperators
open Filter

/-- Concrete finite-state data for the zero-temperature limit of a Gibbs family on a carry
observable. The family `gibbsFamily β` is assumed to converge pointwise to `zeroTempLimit`, and
positive mass in the limit is already known to lie on carry-free states. -/
structure KernelZeroTempData where
  α : Type
  [instFintype : Fintype α]
  [instDecidableEq : DecidableEq α]
  gibbsFamily : ℕ → α → ℝ
  carry : α → ℕ
  zeroTempLimit : α → ℝ
  carryFreeRoot : α
  limitTendsto :
    ∀ a, Tendsto (fun β : ℕ => gibbsFamily β a) atTop (nhds (zeroTempLimit a))
  limitHasTotalMass : ∑ a, zeroTempLimit a = 1
  positiveMassImpliesCarryFree : ∀ a, zeroTempLimit a ≠ 0 → carry a = 0

attribute [instance] KernelZeroTempData.instFintype
attribute [instance] KernelZeroTempData.instDecidableEq

namespace KernelZeroTempData

/-- The finite-state Gibbs family admits a pointwise zero-temperature limit. -/
def zeroTemperatureLimitExists (D : KernelZeroTempData) : Prop :=
  ∃ μ : D.α → ℝ, ∀ a, Tendsto (fun β : ℕ => D.gibbsFamily β a) atTop (nhds (μ a))

/-- The limiting mass is concentrated on the carry-free locus. -/
def limitSupportedOnCarryFree (D : KernelZeroTempData) : Prop :=
  Omega.Conclusion.carryZeroTempSupportMass D.carry D.zeroTempLimit = 1

/-- The carry-free subgraph has a unique essential component, represented here by a distinguished
root state. -/
def uniqueCarryFreeComponent (D : KernelZeroTempData) : Prop :=
  ∀ a, D.carry a = 0 → a = D.carryFreeRoot

/-- Under uniqueness of the carry-free component, the limiting measure is the corresponding
Parry/Dirac measure. -/
def limitIsParryOnUniqueComponent (D : KernelZeroTempData) : Prop :=
  D.zeroTempLimit = Omega.Conclusion.carryFreeParryMeasure D.carryFreeRoot

lemma support_mass_eq_one (D : KernelZeroTempData) :
    Omega.Conclusion.carryZeroTempSupportMass D.carry D.zeroTempLimit = 1 := by
  have hcollapse :
      Omega.Conclusion.carryZeroTempSupportMass D.carry D.zeroTempLimit = ∑ a, D.zeroTempLimit a := by
    unfold Omega.Conclusion.carryZeroTempSupportMass
    calc
      (Finset.univ.filter fun a => D.carry a = 0).sum D.zeroTempLimit
          = ∑ a, if D.carry a = 0 then D.zeroTempLimit a else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ a, D.zeroTempLimit a := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        by_cases hCarry : D.carry a = 0
        · simp [hCarry]
        · have hMass : D.zeroTempLimit a = 0 := by
            by_contra hne
            exact hCarry (D.positiveMassImpliesCarryFree a hne)
          simp [hCarry, hMass]
  calc
    Omega.Conclusion.carryZeroTempSupportMass D.carry D.zeroTempLimit = ∑ a, D.zeroTempLimit a :=
      hcollapse
    _ = 1 := D.limitHasTotalMass

end KernelZeroTempData

open KernelZeroTempData

/-- Paper label: `thm:kernel-zero-temp`. -/
theorem paper_kernel_zero_temp (D : KernelZeroTempData) :
    D.zeroTemperatureLimitExists ∧ D.limitSupportedOnCarryFree ∧
      (D.uniqueCarryFreeComponent → D.limitIsParryOnUniqueComponent) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨D.zeroTempLimit, D.limitTendsto⟩
  · simpa [KernelZeroTempData.limitSupportedOnCarryFree] using D.support_mass_eq_one
  · intro hUnique
    have hCollapse :=
      Omega.Conclusion.paper_conclusion_carry_zero_temp_support_collapse D.carry D.zeroTempLimit
        D.carryFreeRoot D.limitHasTotalMass D.positiveMassImpliesCarryFree hUnique
    simpa [KernelZeroTempData.limitIsParryOnUniqueComponent] using hCollapse.2

end Omega.EA
