import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- Audited standard deviations of the five `c`-slices in the `(3,3,5)` tensor. -/
def arity335LocalizedAbCouplingSd : Fin 5 → ℚ
  | 0 => 347585 / 1000000
  | 1 => 591959 / 10000000
  | 2 => 257971 / 50000000
  | 3 => 787443 / 1000000000
  | 4 => 137309 / 1000000000

/-- Concrete statement recording the audited slice deviations and the tail localization bounds for
`c ≥ 2`. -/
def Arity335LocalizedAbCouplingStatement : Prop :=
  arity335LocalizedAbCouplingSd 0 = 347585 / 1000000 ∧
    arity335LocalizedAbCouplingSd 1 = 591959 / 10000000 ∧
    arity335LocalizedAbCouplingSd 2 = 257971 / 50000000 ∧
    arity335LocalizedAbCouplingSd 3 = 787443 / 1000000000 ∧
    arity335LocalizedAbCouplingSd 4 = 137309 / 1000000000 ∧
    (∀ c : Fin 5, 2 ≤ c.1 → arity335LocalizedAbCouplingSd c ≤ 257971 / 50000000) ∧
    arity335LocalizedAbCouplingSd 3 ≤ 1 / 1000 ∧
    arity335LocalizedAbCouplingSd 4 ≤ 1 / 1000

/-- Paper label: `cor:arity-335-localized-ab-coupling`. -/
theorem paper_arity_335_localized_ab_coupling : Arity335LocalizedAbCouplingStatement := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro c hc
    fin_cases c
    · norm_num at hc
    · norm_num at hc
    · norm_num [arity335LocalizedAbCouplingSd]
    · norm_num [arity335LocalizedAbCouplingSd]
    · norm_num [arity335LocalizedAbCouplingSd]
  · norm_num [arity335LocalizedAbCouplingSd]
  · norm_num [arity335LocalizedAbCouplingSd]

end Omega.Zeta
