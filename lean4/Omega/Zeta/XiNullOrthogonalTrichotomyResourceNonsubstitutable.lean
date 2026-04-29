import Mathlib.Tactic
import Omega.RecursiveAddressing.NullAsH2Obstruction
import Omega.Zeta.XiNullThreeWay

namespace Omega.Zeta

open Omega.RecursiveAddressing.FocusedNonNullReadoutCriterion

/-- The off-slice `NULL` verdict simultaneously records semantic invisibility and protocol-level
rejection. -/
def xiOffSliceOrInvisible (L : ℝ) (s : ℂ) : Prop :=
  xiSemanticNullBranch L s ∧ xiProtocolNullBranch L s

/-- A surviving Čech-`H²` obstruction forces the recursive typed readout to collapse to `NULL`. -/
def xiH2ObstructionForcesNull
    {State Ref Value : Type} [DecidableEq Value]
    (Adm : State → Set Ref) (Vis : State → Ref → Set Value) (p : State) (r : Ref) : Prop :=
  typedReadout Adm Vis p r = Readout.null

/-- Concrete threshold predicates for the three resource axes. -/
def xiVisibleBudgetPassed (budget visibleNeed : ℕ) : Prop := visibleNeed ≤ budget

/-- Concrete threshold predicates for the three resource axes. -/
def xiRegisterBudgetPassed (budget registerNeed : ℕ) : Prop := registerNeed ≤ budget

/-- Concrete threshold predicates for the three resource axes. -/
def xiModeBudgetPassed (budget modeNeed : ℕ) : Prop := modeNeed ≤ budget

/-- A legal readout must satisfy all three resource thresholds simultaneously. -/
def xiLegalReadout (budget visibleNeed registerNeed modeNeed : ℕ) : Prop :=
  xiVisibleBudgetPassed budget visibleNeed ∧
    xiRegisterBudgetPassed budget registerNeed ∧
    xiModeBudgetPassed budget modeNeed

/-- No threshold can substitute for another: each missing axis blocks a legal readout even when the
other two pass. -/
def xiResourceThresholdsAreIndependent (budget visibleNeed registerNeed modeNeed : ℕ) : Prop :=
  ((xiRegisterBudgetPassed budget registerNeed ∧ xiModeBudgetPassed budget modeNeed ∧
      ¬ xiVisibleBudgetPassed budget visibleNeed) →
    ¬ xiLegalReadout budget visibleNeed registerNeed modeNeed) ∧
  ((xiVisibleBudgetPassed budget visibleNeed ∧ xiModeBudgetPassed budget modeNeed ∧
      ¬ xiRegisterBudgetPassed budget registerNeed) →
    ¬ xiLegalReadout budget visibleNeed registerNeed modeNeed) ∧
  ((xiVisibleBudgetPassed budget visibleNeed ∧ xiRegisterBudgetPassed budget registerNeed ∧
      ¬ xiModeBudgetPassed budget modeNeed) →
    ¬ xiLegalReadout budget visibleNeed registerNeed modeNeed)

/-- The `xi` trichotomy wrapper combines the existing semantic/protocol `NULL` split, the
recursive-addressing `H²` obstruction theorem, and the independence of the three resource
thresholds.
    thm:xi-null-orthogonal-trichotomy-resource-nonsubstitutable -/
theorem paper_xi_null_orthogonal_trichotomy_resource_nonsubstitutable
    {A X R : Type*} [Fintype A] [Fintype R] [DecidableEq X]
    {State Ref Value Section Piece ι Cech2 : Type} [DecidableEq Value] [Inhabited Piece]
    {L : ℝ} {s : ℂ}
    (hL : 1 < L) (hs : s.re ≠ 1 / 2)
    (fold : A → X) (reg : A → R)
    (hinj : Function.Injective (fun a => (fold a, reg a)))
    (budget visibleNeed registerNeed modeNeed : ℕ)
    (Adm : State → Set Ref) (Vis Γ : State → Ref → Set Value)
    (GlobalCert : Ref → Set Section)
    (restrict : ι → Section → Piece)
    (transition : ι → ι → Piece → Piece → Cech2)
    (zero : Cech2)
    (ObstructionVanishes : Ref → Prop)
    {p : State} {r : Ref}
    (hΓ : ∀ p r, Γ p r = {v | Vis p r = {v}})
    (hAdm : r ∈ Adm p)
    (hFiber : (GlobalCert r).Nonempty ↔ (Γ p r).Nonempty)
    (hVisEmpty : Γ p r = ∅ → Vis p r = ∅)
    (hvanish_of_global :
      ∀ {sec : Section}, sec ∈ GlobalCert r →
        (∀ i j, transition i j (restrict i sec) (restrict j sec) = zero) →
          ObstructionVanishes r)
    (htransition_trivial :
      ∀ i j {sec : Section}, sec ∈ GlobalCert r →
        transition i j (restrict i sec) (restrict j sec) = zero)
    (hH2 : ¬ ObstructionVanishes r) :
    xiOffSliceOrInvisible L s ∧
      xiH2ObstructionForcesNull Adm Vis p r ∧
      xiResourceThresholdsAreIndependent budget visibleNeed registerNeed modeNeed := by
  rcases paper_xi_null_three_way hL hs fold reg hinj with
    ⟨hSemantic, hProtocol, _, _, _, _⟩
  rcases Omega.RecursiveAddressing.paper_recursive_addressing_null_as_h2_obstruction
      (State := State) (Ref := Ref) (Value := Value) (Section := Section) (Piece := Piece)
      (ι := ι) (Cech2 := Cech2)
      Adm Vis Γ GlobalCert restrict transition zero ObstructionVanishes
      (p := p) (r := r)
      hΓ hAdm hFiber hVisEmpty hvanish_of_global htransition_trivial hH2 with
    ⟨_, _, hNull⟩
  refine ⟨⟨hSemantic, hProtocol⟩, hNull, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _, hVisibleFail⟩ hLegal
    exact hVisibleFail hLegal.1
  · rintro ⟨_, _, hRegisterFail⟩ hLegal
    exact hRegisterFail hLegal.2.1
  · rintro ⟨_, _, hModeFail⟩ hLegal
    exact hModeFail hLegal.2.2

end Omega.Zeta
