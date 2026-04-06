import Omega.Folding.CarryDefect
import Omega.Folding.Defect
import Omega.Folding.FiberArithmeticProperties
import Omega.Folding.FiberRing

namespace Omega

namespace X

noncomputable section

/-! ## Modular mapping tower: modularProject–restrict equivalence and tower properties -/

/-! ### Auxiliary: re-derive stableValue(restrict z) = stableValue z % G -/

/-- stableValue(restrict z) = stableValue z % F(m+2). -/
private theorem stableValue_restrict_eq_mod_tower (z : X (m + 1)) :
    stableValue (X.restrict z) = stableValue z % Nat.fib (m + 2) := by
  have h1 := stableValue_restrict_mod z
  have h2 := stableValue_lt_fib (X.restrict z)
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1.symm

/-! ### Theorem 1: modularProject = restrict -/

/-- modularProject equals restrict as functions X(m+1) → X(m).
    Both produce the unique stable word with value stableValue(x) % F(m+2).
    thm:pom-modular-project-eq-restrict -/
theorem modularProject_eq_restrict (x : X (m + 1)) :
    modularProject x = X.restrict x := by
  apply eq_of_stableValue_eq
  rw [stableValue_modularProject, ← stableValue_restrict_eq_mod_tower]

/-! ### Theorem 2: modularProject carry defect for addition -/

/-- modularProject carry defect for addition (via restrict equivalence).
    Paper: thm:pom-stable-addition-carry-defect-unique-element (modularProject form) -/
theorem modularProject_stableAdd_carry (x y : X (m + 1)) :
    modularProject (stableAdd x y) =
      stableAdd (stableAdd (modularProject x) (modularProject y))
        (if carryIndicator x y = 0 then stableZero else carryElement m) := by
  rw [modularProject_eq_restrict, modularProject_eq_restrict x, modularProject_eq_restrict y]
  exact restrict_stableAdd_carry_defect x y

/-! ### Theorem 3: multiplicative projection value identity -/

/-- Value-level identity for multiplicative projection through the tower.
    thm:pom-modular-project-mul-value -/
theorem stableValue_modularProject_stableMul (x y : X (m + 1)) :
    stableValue (modularProject (stableMul x y)) =
      (stableValue x * stableValue y) % Nat.fib (m + 3) % Nat.fib (m + 2) := by
  rw [stableValue_modularProject, stableValue_stableMul]

/-- Multiplicative projection via restrict.
    thm:pom-restrict-mul-value -/
theorem stableValue_restrict_stableMul (x y : X (m + 1)) :
    stableValue (X.restrict (stableMul x y)) =
      (stableValue x * stableValue y) % Nat.fib (m + 3) % Nat.fib (m + 2) := by
  rw [stableValue_restrict_eq_mod_tower, stableValue_stableMul]

/-! ### Theorem 4: restrict compose equals restrictLE -/

/-- Two applications of restrict equal the composed restrictLE.
    thm:pom-restrict-comp-restrict -/
theorem restrict_comp_restrict (x : X (m + 2)) :
    X.restrict (X.restrict x) =
      X.restrictLE (Nat.le_trans (Nat.le_succ m) (Nat.le_succ (m + 1))) x := by
  conv_lhs =>
    rw [show X.restrict x = X.restrictLE (Nat.le_succ (m + 1)) x from
      (X.restrictLE_succ x).symm]
    rw [show X.restrict (X.restrictLE (Nat.le_succ (m + 1)) x) =
      X.restrictLE (Nat.le_succ m) (X.restrictLE (Nat.le_succ (m + 1)) x) from
      (X.restrictLE_succ (X.restrictLE (Nat.le_succ (m + 1)) x)).symm]
  exact X.restrictLE_comp (Nat.le_succ m) (Nat.le_succ (m + 1)) x

/-! ### Theorem 5: tower compatibility -/

/-- The tower of restriction maps is compatible: restrict ∘ restrict = restrictLE.
    thm:pom-tower-compatible -/
theorem tower_compatible (x : X (m + 2)) :
    X.restrict (X.restrict x) = X.restrictLE (Nat.le_succ m) (X.restrict x) := by
  rw [X.restrictLE_succ]

/-! ### Theorem 6: restrict transitivity -/

/-- restrict composes correctly via restrictLE transitivity.
    thm:pom-restrict-tower-transitivity -/
theorem restrict_tower_transitivity (h₁ : m ≤ n) (x : X (n + 1)) :
    X.restrictLE h₁ (X.restrict x) =
      X.restrictLE (Nat.le_trans h₁ (Nat.le_succ n)) x := by
  exact (X.restrictLE_trans_succ h₁ x).symm

/-! ### Theorem 7: modularProject preserves zero -/

/-- modularProject preserves the zero element.
    thm:pom-modular-project-zero -/
theorem modularProject_stableZero :
    modularProject (stableZero (m := m + 1)) = (stableZero : X m) :=
  modularProject_zero

/-! ### Additional tower properties -/

/-- Value-level carry defect for modularProject addition.
    thm:pom-modular-project-add-carry-value -/
theorem stableValue_modularProject_stableAdd_carry (x y : X (m + 1)) :
    stableValue (modularProject (stableAdd x y)) =
      (stableValue (modularProject x) + stableValue (modularProject y) +
        carryIndicator x y * Nat.fib m) % Nat.fib (m + 2) := by
  rw [modularProject_eq_restrict, modularProject_eq_restrict x, modularProject_eq_restrict y]
  exact stableValue_restrict_stableAdd_carry x y

/-- modularProject composes through two levels via double mod.
    thm:pom-modular-project-compose-value -/
theorem stableValue_modularProject_compose (x : X (m + 2)) :
    stableValue (modularProject (m := m) (modularProject (m := m + 1) x)) =
      stableValue x % Nat.fib (m + 3) % Nat.fib (m + 2) := by
  rw [stableValue_modularProject, stableValue_modularProject]

/-- The carry indicator is symmetric.
    thm:pom-carry-indicator-comm -/
theorem carryIndicator_comm (x y : X (m + 1)) :
    carryIndicator x y = carryIndicator y x := by
  unfold carryIndicator; rw [Nat.add_comm]

/-- The modularProject tower: surjectivity at every level.
    thm:pom-modular-tower-surjective -/
theorem modularProject_tower_surjective (m : Nat) :
    Function.Surjective (modularProject (m := m)) :=
  modularProject_surjective m

end

/-- restrict preserves zero: restrict(0) = 0.
    restrict-zero -/
theorem restrict_zero : X.restrict (0 : X (m + 1)) = (0 : X m) := by
  show X.restrict (stableZero) = stableZero
  apply Subtype.ext; funext i
  simp [stableZero, X.ofNat, X.ofIndices, X.wordOfIndices, X.restrict, truncate]

/-- restrict preserves one: restrict(1) = 1.
    restrict-one -/
theorem restrict_one : X.restrict (1 : X (m + 1)) = (1 : X m) := by
  show X.restrict (stableOne) = stableOne
  apply Subtype.ext; funext i
  simp [stableOne, X.ofNat, X.ofIndices, X.wordOfIndices, X.restrict, truncate]

/-- restrict is surjective (from modularProject surjectivity).
    prop:restrict-surjective -/
theorem restrict_surjective : Function.Surjective (X.restrict (m := m)) := by
  intro y
  obtain ⟨x, hx⟩ := modularProject_surjective m y
  exact ⟨x, (modularProject_eq_restrict x).symm.trans hx⟩

/-- The restrict fiber of y is nonempty (from surjectivity).
    cor:restrict-fiber-nonempty -/
theorem restrict_fiber_nonempty (y : X m) :
    ∃ x : X (m + 1), X.restrict x = y :=
  restrict_surjective y

-- ══════════════════════════════════════════════════════════════
-- Phase R322: modularProject preserves one and negation value
-- ══════════════════════════════════════════════════════════════

/-- modularProject preserves the one element.
    thm:pom-stable-addition-carry-defect-unique-element -/
theorem modularProject_stableOne (hm : 1 ≤ m) :
    modularProject (stableOne (m := m + 1)) = (stableOne : X m) := by
  apply eq_of_stableValue_eq
  rw [stableValue_modularProject, stableValue_stableOne_of_ge_one (by omega : 1 ≤ m + 1),
      Nat.mod_eq_of_lt (fib_gt_one_of_ge_two hm),
      stableValue_stableOne_of_ge_one hm]

end X

end Omega
