import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- A single scalar congruence fiber modulo `b`. -/
def xi_smith_pk_congruence_solvability_count_scalarFiber (b s : ℕ) (c : ZMod b) : Type :=
  {x : ZMod b // (s : ZMod b) * x = c}

/-- The diagonal Smith-congruence system obtained after invertible row and column changes. -/
def xi_smith_pk_congruence_solvability_count_diagonalSystem {n d b : ℕ} (s : Fin n → ℕ)
    (C : Fin n → Fin d → ZMod b) (X : Fin n → Fin d → ZMod b) : Prop :=
  ∀ i j, (s i : ZMod b) * X i j = C i j

/-- The solution matrix of a diagonal Smith system is exactly a product of independent scalar
congruence fibers, one for each row and column coordinate. -/
def xi_smith_pk_congruence_solvability_count_solutionEquiv {n d b : ℕ} (s : Fin n → ℕ)
    (C : Fin n → Fin d → ZMod b) :
    {X : Fin n → Fin d → ZMod b //
        xi_smith_pk_congruence_solvability_count_diagonalSystem s C X} ≃
      ((i : Fin n) → (j : Fin d) →
        xi_smith_pk_congruence_solvability_count_scalarFiber b (s i) (C i j)) where
  toFun X i j := ⟨X.1 i j, X.2 i j⟩
  invFun Y := ⟨fun i j => (Y i j).1, fun i j => (Y i j).2⟩
  left_inv X := by
    rcases X with ⟨X, hX⟩
    rfl
  right_inv Y := by
    funext i j
    apply Subtype.ext
    rfl

/-- Paper label: `prop:xi-smith-pk-congruence-solvability-count`.

After Smith reduction to a diagonal system modulo a prime power, the matrix-congruence solution
set factors into independent scalar congruence fibers. Consequently its cardinality is the product
of the scalar solution counts over all rows and columns. -/
def xi_smith_pk_congruence_solvability_count_statement : Prop :=
  ∀ (n d b : ℕ) (s : Fin n → ℕ) (C : Fin n → Fin d → ZMod b),
    Nat.card
        {X : Fin n → Fin d → ZMod b //
          xi_smith_pk_congruence_solvability_count_diagonalSystem s C X} =
      ∏ i : Fin n, ∏ j : Fin d,
        Nat.card (xi_smith_pk_congruence_solvability_count_scalarFiber b (s i) (C i j))

theorem paper_xi_smith_pk_congruence_solvability_count :
    xi_smith_pk_congruence_solvability_count_statement := by
  intro n d b s C
  calc
    Nat.card
        {X : Fin n → Fin d → ZMod b //
          xi_smith_pk_congruence_solvability_count_diagonalSystem s C X}
        = Nat.card
            ((i : Fin n) → (j : Fin d) →
              xi_smith_pk_congruence_solvability_count_scalarFiber b (s i) (C i j)) := by
          exact Nat.card_congr
            (xi_smith_pk_congruence_solvability_count_solutionEquiv s C)
    _ = ∏ i : Fin n, Nat.card
            ((j : Fin d) →
              xi_smith_pk_congruence_solvability_count_scalarFiber b (s i) (C i j)) := by
          rw [Nat.card_pi]
    _ = ∏ i : Fin n, ∏ j : Fin d,
            Nat.card
              (xi_smith_pk_congruence_solvability_count_scalarFiber b (s i) (C i j)) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [Nat.card_pi]

end Omega.Zeta
