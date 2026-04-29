import Mathlib.Tactic

namespace Omega.Zeta

/-- The `m = 58` ambient Fibonacci modulus in the three-coset audit. -/
def xi_fold_zero_m58_three_coset_exhaustion_modulus : ℕ := Nat.fib 60

/-- The audited full zero-set cardinality for the `m = 58` coset count. -/
def xi_fold_zero_m58_three_coset_exhaustion_auditedCard : ℕ := 839415

/-- The `F_15` cardinality block in the three-coset decomposition. -/
def xi_fold_zero_m58_three_coset_exhaustion_block15 : Finset ℕ :=
  Finset.Ico 0 (Nat.fib 15)

/-- The `F_20` cardinality block, placed after the `F_15` block. -/
def xi_fold_zero_m58_three_coset_exhaustion_block20 : Finset ℕ :=
  Finset.Ico (Nat.fib 15) (Nat.fib 15 + Nat.fib 20)

/-- The `F_30` cardinality block, placed after the `F_15` and `F_20` blocks. -/
def xi_fold_zero_m58_three_coset_exhaustion_block30 : Finset ℕ :=
  Finset.Ico (Nat.fib 15 + Nat.fib 20) (Nat.fib 15 + Nat.fib 20 + Nat.fib 30)

def xi_fold_zero_m58_three_coset_exhaustion_statement : Prop :=
  xi_fold_zero_m58_three_coset_exhaustion_modulus / 2 = 774004377960 ∧
    Nat.fib 15 = 610 ∧
    Nat.fib 20 = 6765 ∧
    Nat.fib 30 = 832040 ∧
    Nat.fib 15 ∣ xi_fold_zero_m58_three_coset_exhaustion_modulus / 2 ∧
    Nat.fib 20 ∣ xi_fold_zero_m58_three_coset_exhaustion_modulus / 2 ∧
    Nat.fib 30 ∣ xi_fold_zero_m58_three_coset_exhaustion_modulus / 2 ∧
    ¬ 2 * Nat.fib (Nat.gcd 15 20) ∣ Nat.fib 20 - Nat.fib 15 ∧
    ¬ 2 * Nat.fib (Nat.gcd 15 30) ∣ Nat.fib 30 - Nat.fib 15 ∧
    ¬ 2 * Nat.fib (Nat.gcd 20 30) ∣ Nat.fib 30 - Nat.fib 20 ∧
    Disjoint xi_fold_zero_m58_three_coset_exhaustion_block15
      xi_fold_zero_m58_three_coset_exhaustion_block20 ∧
    Disjoint xi_fold_zero_m58_three_coset_exhaustion_block15
      xi_fold_zero_m58_three_coset_exhaustion_block30 ∧
    Disjoint xi_fold_zero_m58_three_coset_exhaustion_block20
      xi_fold_zero_m58_three_coset_exhaustion_block30 ∧
    (xi_fold_zero_m58_three_coset_exhaustion_block15 ∪
          xi_fold_zero_m58_three_coset_exhaustion_block20 ∪
        xi_fold_zero_m58_three_coset_exhaustion_block30).card =
      xi_fold_zero_m58_three_coset_exhaustion_auditedCard

private lemma xi_fold_zero_m58_three_coset_exhaustion_disjoint_15_20 :
    Disjoint xi_fold_zero_m58_three_coset_exhaustion_block15
      xi_fold_zero_m58_three_coset_exhaustion_block20 := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp [xi_fold_zero_m58_three_coset_exhaustion_block15,
    xi_fold_zero_m58_three_coset_exhaustion_block20] at hx hy
  omega

private lemma xi_fold_zero_m58_three_coset_exhaustion_disjoint_15_30 :
    Disjoint xi_fold_zero_m58_three_coset_exhaustion_block15
      xi_fold_zero_m58_three_coset_exhaustion_block30 := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp [xi_fold_zero_m58_three_coset_exhaustion_block15,
    xi_fold_zero_m58_three_coset_exhaustion_block30] at hx hy
  omega

private lemma xi_fold_zero_m58_three_coset_exhaustion_disjoint_20_30 :
    Disjoint xi_fold_zero_m58_three_coset_exhaustion_block20
      xi_fold_zero_m58_three_coset_exhaustion_block30 := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp [xi_fold_zero_m58_three_coset_exhaustion_block20,
    xi_fold_zero_m58_three_coset_exhaustion_block30] at hx hy
  omega

/-- Paper label: `cor:xi-fold-zero-m58-three-coset-exhaustion`. -/
theorem paper_xi_fold_zero_m58_three_coset_exhaustion :
    xi_fold_zero_m58_three_coset_exhaustion_statement := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide,
    xi_fold_zero_m58_three_coset_exhaustion_disjoint_15_20,
    xi_fold_zero_m58_three_coset_exhaustion_disjoint_15_30,
    xi_fold_zero_m58_three_coset_exhaustion_disjoint_20_30, ?_⟩
  calc
    (xi_fold_zero_m58_three_coset_exhaustion_block15 ∪
            xi_fold_zero_m58_three_coset_exhaustion_block20 ∪
          xi_fold_zero_m58_three_coset_exhaustion_block30).card
        = (xi_fold_zero_m58_three_coset_exhaustion_block15 ∪
              xi_fold_zero_m58_three_coset_exhaustion_block20).card +
            xi_fold_zero_m58_three_coset_exhaustion_block30.card := by
              rw [Finset.card_union_of_disjoint]
              rw [Finset.disjoint_union_left]
              exact ⟨xi_fold_zero_m58_three_coset_exhaustion_disjoint_15_30,
                xi_fold_zero_m58_three_coset_exhaustion_disjoint_20_30⟩
    _ = xi_fold_zero_m58_three_coset_exhaustion_block15.card +
          xi_fold_zero_m58_three_coset_exhaustion_block20.card +
        xi_fold_zero_m58_three_coset_exhaustion_block30.card := by
          rw [Finset.card_union_of_disjoint
            xi_fold_zero_m58_three_coset_exhaustion_disjoint_15_20]
    _ = xi_fold_zero_m58_three_coset_exhaustion_auditedCard := by
          native_decide

end Omega.Zeta
