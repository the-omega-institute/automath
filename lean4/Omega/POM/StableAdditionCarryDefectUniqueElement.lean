import Omega.Folding.ModularTower

namespace Omega.POM

/-- Mod-`F_{m+2}` carry rewrite used in the stable-addition defect package: subtracting the
upper-level modulus `F_{m+3}` is equivalent to adding the carry value `F_m`. -/
private theorem pom_stable_addition_carry_defect_unique_element_mod_fib_carry_rewrite (m : ℕ) :
    (Nat.fib (m + 3) + Nat.fib m) % Nat.fib (m + 2) = 0 := by
  have hFG : Nat.fib (m + 3) = Nat.fib (m + 2) + Nat.fib (m + 1) := Omega.fib_succ_succ' (m + 1)
  have hGfib : Nat.fib (m + 1) + Nat.fib m = Nat.fib (m + 2) := Omega.X.fib_succ_add_fib_eq m
  have hrewrite : Nat.fib (m + 3) + Nat.fib m = 2 * Nat.fib (m + 2) := by
    omega
  rw [hrewrite, two_mul, Nat.add_mod]
  simp

/-- Paper-facing statement for the stable-addition carry-defect identity together with the unique
carry element and the Fibonacci congruence data used in the paper proof. -/
def pom_stable_addition_carry_defect_unique_element_statement : Prop :=
  (∀ m : ℕ, ∀ x y : Omega.X (m + 1),
    Omega.X.modularProject (Omega.X.stableAdd x y) =
      Omega.X.stableAdd (Omega.X.stableAdd (Omega.X.modularProject x) (Omega.X.modularProject y))
        (if Omega.carryIndicator x y = 0 then Omega.X.stableZero else Omega.X.carryElement m)) ∧
    (∀ m : ℕ, ∀ x y : Omega.X m,
      (Omega.stableValue x + Omega.stableValue y) / Nat.fib (m + 2) ≤ 1) ∧
    (∀ m : ℕ, 1 ≤ m →
      Omega.X.modularProject (Omega.X.stableOne (m := m + 1)) = (Omega.X.stableOne : Omega.X m)) ∧
    (∀ m : ℕ, Omega.stableValue (Omega.X.carryElement m) = Nat.fib m) ∧
    (∀ m : ℕ, ∀ z : Omega.X m, Omega.stableValue z = Nat.fib m → z = Omega.X.carryElement m) ∧
    (∀ m : ℕ, Nat.fib m + Nat.fib (m + 1) = Nat.fib (m + 2)) ∧
    (∀ m : ℕ, (Nat.fib (m + 3) + Nat.fib m) % Nat.fib (m + 2) = 0)

/-- Paper label: `thm:pom-stable-addition-carry-defect-unique-element`. This packages the
carry-defect identity, the binary carry bound, the compatibility of `stableOne` with
`modularProject`, the Fibonacci value of the carry element, its uniqueness as the value-`F_m`
element, and the Fibonacci congruence rewrite underlying the defect term. -/
theorem paper_pom_stable_addition_carry_defect_unique_element :
    pom_stable_addition_carry_defect_unique_element_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    pom_stable_addition_carry_defect_unique_element_mod_fib_carry_rewrite⟩
  · intro m x y
    exact Omega.X.modularProject_stableAdd_carry x y
  · intro m x y
    exact Omega.stableAdd_carry_binary x y
  · intro m hm
    exact Omega.X.modularProject_stableOne hm
  · intro m
    simpa using (Omega.X.stableValue_carryElement (m := m))
  · intro m z hz
    exact Omega.X.eq_of_stableValue_eq
      (hz.trans (Omega.X.stableValue_carryElement (m := m)).symm)
  · intro m
    have h := Omega.fib_succ_succ' m
    omega

/-- Paper label: `cor:pom-carry-defect-m6-anchor-8-34`. The stable-addition carry element at
level `6` has the Fibonacci value `F_6 = 8`, and the adjacent anchor numerals are `F_8 = 21`
and `F_9 = 34`. -/
theorem paper_pom_carry_defect_m6_anchor_8_34 :
    Nat.fib 8 = 21 ∧ Nat.fib 9 = 34 ∧
      Omega.stableValue (Omega.X.carryElement 6) = 8 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simpa using (Omega.X.stableValue_carryElement (m := 6))

end Omega.POM
