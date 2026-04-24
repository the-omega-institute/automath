import Mathlib.Tactic
import Omega.POM.DoubleTransversalNormalForm
import Omega.POM.ExtendedPrimitives

namespace Omega.POM

open Omega.POM.DoubleTransversalNormalForm

/-- The stable-address transversal is applied only once, at the terminal output stage. -/
def pomTerminalFoldCalls (_D : ExtendedPrimitiveData) : ℕ := 1

/-- The quotient/remainder transversal is applied only once, at the terminal output stage. -/
def pomTerminalPiCalls (_D : ExtendedPrimitiveData) : ℕ := 1

/-- Concrete process-layer version of the projection-budget corollary: the extended primitives
already compute internally in normal form, the optional quotient/remainder readout can be deferred
to one terminal symmetric decomposition, and the final projection steps are genuinely needed
because values and congruence classes admit multiple representatives before choosing a section. -/
def PomProjectionBudget (D : ExtendedPrimitiveData) : Prop :=
  D.processLayerNormalForm ∧
    pomTerminalFoldCalls D = 1 ∧
    pomTerminalPiCalls D = 1 ∧
    (∀ a b : ℕ,
      (a : ℤ) = symQuo (a : ℤ) (b + 1) * (b + 1) + symRem (a : ℤ) (b + 1)) ∧
    (∃ x y : Config, x ≠ y ∧ val x = val y) ∧
    (∃ n₁ n₂ : ℤ, n₁ ≠ n₂ ∧ symRem n₁ 2 = symRem n₂ 2)

/-- Paper label: `cor:pom-projection-budget`. -/
theorem paper_pom_projection_budget (D : ExtendedPrimitiveData) : PomProjectionBudget D := by
  rcases paper_pom_extended_primitives D with ⟨_, _, _, _, _, hNormalForm⟩
  refine ⟨hNormalForm, rfl, rfl, ?_, ?_, ?_⟩
  · intro a b
    exact symQuoRem_spec (a : ℤ) (b + 1) (Nat.succ_pos b)
  · refine ⟨Finsupp.single 0 2, Finsupp.single 1 1, ?_, ?_⟩
    · intro hEq
      have h0 := congrArg (fun f : Config => f 0) hEq
      simp at h0
    · rw [val, val, Omega.EA.valPr_single, Omega.EA.valPr_single]
      norm_num
  · refine ⟨0, 2, by decide, ?_⟩
    norm_num [symRem]

end Omega.POM
