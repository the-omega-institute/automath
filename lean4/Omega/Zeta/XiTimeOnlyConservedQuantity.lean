import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete seed model for the time-only conservation statement.

Morphisms are natural lengths, composition is addition, and the only basic reversible
generator is the null move. This captures the quotient in which cycle contributions have
been killed and only elapsed time remains. -/
structure xi_time_only_conserved_quantity_system where
  marker : Unit := ()

namespace xi_time_only_conserved_quantity_system

/-- Morphisms in the seeded quotient are represented by their elapsed time. -/
abbrev Mor (_C : xi_time_only_conserved_quantity_system) : Type := ℕ

/-- The null move is the reversible basic generator after quotienting cycles. -/
def BasicReversible (_C : xi_time_only_conserved_quantity_system) (e : ℕ) : Prop :=
  e = 0

/-- In the time quotient, every pair of elapsed-time morphisms composes. -/
def Composable (_C : xi_time_only_conserved_quantity_system) (_u _v : ℕ) : Prop :=
  True

/-- Composition adds elapsed lengths. -/
def comp (_C : xi_time_only_conserved_quantity_system) (u v : ℕ) : ℕ :=
  u + v

/-- The conserved time length of a morphism. -/
def length (_C : xi_time_only_conserved_quantity_system) (w : ℕ) : ℝ :=
  (w : ℝ)

end xi_time_only_conserved_quantity_system

/-- Paper label: `thm:xi-time-only-conserved-quantity`. In the seeded time quotient, any real
additive invariant that vanishes on the reversible null generator is a scalar multiple of
elapsed length. -/
theorem paper_xi_time_only_conserved_quantity
    (C : xi_time_only_conserved_quantity_system) (I : C.Mor -> ℝ)
    (hbasic : ∀ e, C.BasicReversible e -> I e = 0)
    (hadd : ∀ {u v}, C.Composable u v -> I (C.comp u v) = I u + I v) :
    ∃ lambda : ℝ, ∀ w, I w = lambda * C.length w := by
  refine ⟨I 1, ?_⟩
  intro w
  dsimp [xi_time_only_conserved_quantity_system.Mor,
    xi_time_only_conserved_quantity_system.length]
  induction w with
  | zero =>
      have hzero : I 0 = 0 := hbasic 0 rfl
      simp [hzero]
  | succ n ih =>
      have hstep : I (n + 1) = I n + I 1 := by
        simpa [xi_time_only_conserved_quantity_system.comp,
          xi_time_only_conserved_quantity_system.Composable] using
          (hadd (u := n) (v := 1) trivial)
      calc
        I (Nat.succ n) = I (n + 1) := by rw [Nat.succ_eq_add_one]
        _ = I n + I 1 := hstep
        _ = I 1 * (n : ℝ) + I 1 := by rw [ih]
        _ = I 1 * (Nat.succ n : ℝ) := by
          rw [Nat.cast_succ]
          ring

end Omega.Zeta
