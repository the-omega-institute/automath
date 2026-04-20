import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- The fiber of the fold map over an output address. -/
def xiAddressFiber {A X : Type*} [DecidableEq X] (fold : A → X) (x : X) :=
  {a : A // fold a = x}

/-- Finite fibers inherit a `Fintype` structure from the finite source space. -/
noncomputable instance {A X : Type*} [Fintype A] [DecidableEq X] (fold : A → X) (x : X) :
    Fintype (xiAddressFiber fold x) := by
  classical
  unfold xiAddressFiber
  infer_instance

/-- The cardinality of a fold fiber. -/
noncomputable def xiAddressFiberCard {A X : Type*} [Fintype A] [DecidableEq X]
    (fold : A → X) (x : X) : ℕ :=
  Fintype.card (xiAddressFiber fold x)

/-- A concrete proxy for the conditional entropy budget carried by the auxiliary register. -/
noncomputable def xiConditionalEntropyProxy (R : Type*) [Fintype R] : ℝ :=
  Real.log (Fintype.card R)

/-- Fiberwise injectivization means that equal fold outputs force distinct register values unless
    the source points already coincide. -/
def xiFiberwiseSeparated {A X R : Type*} (fold : A → X) (r : A → R) : Prop :=
  ∀ ⦃a b : A⦄, fold a = fold b → a ≠ b → r a ≠ r b

/-- Every observed fiber pays at most the available register budget. -/
def xiFiberUniformLiftCostBound {A X R : Type*} [Fintype A] [Fintype R] [DecidableEq X]
    (fold : A → X) (_r : A → R) : Prop :=
  ∀ a : A, Real.log (xiAddressFiberCard fold (fold a)) ≤ xiConditionalEntropyProxy R

theorem xiFiberwiseSeparated_of_injective {A X R : Type*} (fold : A → X) (r : A → R)
    (hinj : Function.Injective fun a => (fold a, r a)) :
    xiFiberwiseSeparated fold r := by
  intro a b hab hab_ne hr
  apply hab_ne
  apply hinj
  exact Prod.ext hab hr

theorem xiAddressFiberCard_le_register {A X R : Type*} [Fintype A] [Fintype R] [DecidableEq X]
    (fold : A → X) (r : A → R) (hinj : Function.Injective fun a => (fold a, r a)) (a : A) :
    xiAddressFiberCard fold (fold a) ≤ Fintype.card R := by
  classical
  let encode : xiAddressFiber fold (fold a) → R := fun y => r y.1
  have hencode : Function.Injective encode := by
    intro y z hyz
    exact Subtype.ext <| hinj <| Prod.ext (by simpa using y.2.trans z.2.symm) hyz
  simpa [xiAddressFiberCard, encode] using Fintype.card_le_of_injective encode hencode

theorem xiFiberUniformLiftCostBound_of_injective {A X R : Type*} [Fintype A] [Fintype R]
    [DecidableEq X] (fold : A → X) (r : A → R)
    (hinj : Function.Injective fun a => (fold a, r a)) :
    xiFiberUniformLiftCostBound fold r := by
  intro a
  have hcard := xiAddressFiberCard_le_register fold r hinj a
  have hfiber_pos_nat : 0 < xiAddressFiberCard fold (fold a) := by
    classical
    rw [xiAddressFiberCard]
    let y : xiAddressFiber fold (fold a) := ⟨a, rfl⟩
    exact Fintype.card_pos_iff.mpr ⟨y⟩
  have hR_pos_nat : 0 < Fintype.card R := by
    exact Fintype.card_pos_iff.mpr ⟨r a⟩
  have hfiber_pos : 0 < (xiAddressFiberCard fold (fold a) : ℝ) := by
    exact_mod_cast hfiber_pos_nat
  have hcard_real : (xiAddressFiberCard fold (fold a) : ℝ) ≤ Fintype.card R := by
    exact_mod_cast hcard
  exact Real.log_le_log hfiber_pos hcard_real

/-- Proposition package for the address-defect law: injectivization separates each fiber and the
    register budget dominates the logarithmic fiber cost.
    thm:address-defect-law -/
def paper_xi_address_defect_law_statement : Prop :=
  ∀ {A X R : Type*} [Fintype A] [Fintype R] [DecidableEq X],
    ∀ (fold : A → X) (r : A → R),
      Function.Injective (fun a => (fold a, r a)) →
      xiFiberwiseSeparated fold r ∧ xiFiberUniformLiftCostBound fold r

theorem paper_xi_address_defect_law : paper_xi_address_defect_law_statement := by
  intro A X R _ _ _ fold r hinj
  exact ⟨xiFiberwiseSeparated_of_injective fold r hinj,
    xiFiberUniformLiftCostBound_of_injective fold r hinj⟩

end Omega.Zeta
