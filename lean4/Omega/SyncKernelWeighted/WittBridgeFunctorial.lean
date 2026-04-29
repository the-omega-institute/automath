import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Sequence-valued trace data used by the Witt bridge. -/
abbrev witt_bridge_functorial_sequence := ℕ → ℚ

/-- Componentwise intertwining by a scalar `T`. -/
def witt_bridge_functorial_intertwines (T : ℚ)
    (a b : witt_bridge_functorial_sequence) : Prop :=
  ∀ n : ℕ, b n = T * a n

/-- Ghost transform: multiply the `n`th trace by `n`. -/
def witt_bridge_functorial_ghost (a : witt_bridge_functorial_sequence) :
    witt_bridge_functorial_sequence :=
  fun n => (n : ℚ) * a n

/-- Möbius transform on ghost coordinates. -/
def witt_bridge_functorial_mobius (a : witt_bridge_functorial_sequence) :
    witt_bridge_functorial_sequence :=
  fun n => Finset.sum (Nat.divisors n) fun d =>
    (ArithmeticFunction.moebius d : ℚ) * witt_bridge_functorial_ghost a (n / d)

/-- Euler transform obtained by dividing the Möbius coordinate by `n`. -/
def witt_bridge_functorial_euler (a : witt_bridge_functorial_sequence) :
    witt_bridge_functorial_sequence :=
  fun n => if n = 0 then 0 else (1 / (n : ℚ)) * witt_bridge_functorial_mobius a n

/-- The zeta coordinate is the composed natural transformation `n * Euler_n`. -/
def witt_bridge_functorial_zeta (a : witt_bridge_functorial_sequence) :
    witt_bridge_functorial_sequence :=
  fun n => (n : ℚ) * witt_bridge_functorial_euler a n

lemma witt_bridge_functorial_ghost_natural {T : ℚ} {a b : witt_bridge_functorial_sequence}
    (h : witt_bridge_functorial_intertwines T a b) :
    witt_bridge_functorial_intertwines T
      (witt_bridge_functorial_ghost a) (witt_bridge_functorial_ghost b) := by
  intro n
  simp [witt_bridge_functorial_ghost, h n, mul_assoc, mul_comm]

lemma witt_bridge_functorial_mobius_natural {T : ℚ} {a b : witt_bridge_functorial_sequence}
    (h : witt_bridge_functorial_intertwines T a b) :
    witt_bridge_functorial_intertwines T
      (witt_bridge_functorial_mobius a) (witt_bridge_functorial_mobius b) := by
  intro n
  unfold witt_bridge_functorial_mobius
  calc
    Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℚ) *
        witt_bridge_functorial_ghost b (n / d)
      ) = Finset.sum (Nat.divisors n) (fun d => T * ((ArithmeticFunction.moebius d : ℚ) *
          witt_bridge_functorial_ghost a (n / d)) ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [witt_bridge_functorial_ghost_natural h (n / d)]
          ring
    _ = T * Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℚ) *
          witt_bridge_functorial_ghost a (n / d)) := by
          rw [Finset.mul_sum]

lemma witt_bridge_functorial_euler_natural {T : ℚ} {a b : witt_bridge_functorial_sequence}
    (h : witt_bridge_functorial_intertwines T a b) :
    witt_bridge_functorial_intertwines T
      (witt_bridge_functorial_euler a) (witt_bridge_functorial_euler b) := by
  intro n
  by_cases h0 : n = 0
  · subst h0
    simp [witt_bridge_functorial_euler]
  · simp [witt_bridge_functorial_euler, h0, witt_bridge_functorial_mobius_natural h n,
      mul_left_comm]

lemma witt_bridge_functorial_zeta_natural {T : ℚ} {a b : witt_bridge_functorial_sequence}
    (h : witt_bridge_functorial_intertwines T a b) :
    witt_bridge_functorial_intertwines T
      (witt_bridge_functorial_zeta a) (witt_bridge_functorial_zeta b) := by
  intro n
  simp [witt_bridge_functorial_zeta, witt_bridge_functorial_euler_natural h n, mul_left_comm]

lemma witt_bridge_functorial_zeta_identity (a : witt_bridge_functorial_sequence) {n : ℕ}
    (hn : 0 < n) :
    witt_bridge_functorial_zeta a n = witt_bridge_functorial_mobius a n := by
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hmul : (n : ℚ) * (1 / (n : ℚ)) = 1 := by
    field_simp [hnq]
  calc
    witt_bridge_functorial_zeta a n
      = (n : ℚ) * ((1 / (n : ℚ)) * witt_bridge_functorial_mobius a n) := by
          simp [witt_bridge_functorial_zeta, witt_bridge_functorial_euler, hn.ne']
    _ = ((n : ℚ) * (1 / (n : ℚ))) * witt_bridge_functorial_mobius a n := by
          ring
    _ = witt_bridge_functorial_mobius a n := by
          rw [hmul, one_mul]

/-- Paper label: `prop:witt-bridge-functorial`. Ghost, Möbius, Euler, and zeta coordinates are
sequence-valued transforms. Any scalar intertwiner acts componentwise on traces and therefore
commutes with each transform, while the zeta coordinate is the composed natural transformation
`n * Euler_n = Möbius_n` on every positive degree. -/
theorem paper_witt_bridge_functorial (T : ℚ) (a b : witt_bridge_functorial_sequence)
    (h : witt_bridge_functorial_intertwines T a b) :
    witt_bridge_functorial_intertwines T
        (witt_bridge_functorial_ghost a) (witt_bridge_functorial_ghost b) ∧
      witt_bridge_functorial_intertwines T
        (witt_bridge_functorial_mobius a) (witt_bridge_functorial_mobius b) ∧
      witt_bridge_functorial_intertwines T
        (witt_bridge_functorial_euler a) (witt_bridge_functorial_euler b) ∧
      witt_bridge_functorial_intertwines T
        (witt_bridge_functorial_zeta a) (witt_bridge_functorial_zeta b) ∧
      ∀ n : ℕ, 0 < n →
        witt_bridge_functorial_zeta a n = witt_bridge_functorial_mobius a n ∧
          witt_bridge_functorial_zeta b n = witt_bridge_functorial_mobius b n := by
  refine ⟨witt_bridge_functorial_ghost_natural h, witt_bridge_functorial_mobius_natural h,
    witt_bridge_functorial_euler_natural h, witt_bridge_functorial_zeta_natural h, ?_⟩
  intro n hn
  exact ⟨witt_bridge_functorial_zeta_identity a hn,
    witt_bridge_functorial_zeta_identity b hn⟩

end Omega.SyncKernelWeighted
