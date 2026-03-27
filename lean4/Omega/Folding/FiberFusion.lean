/-
Copyright (c) 2026 The Omega Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fibonacci fusion identity and strict submultiplicativity.

Paper reference: lem:pom-fib-fusion-submultiplicativity, cor:pom-fib-component-fusion-gain
-/
import Omega.Core.Fib

namespace Omega

/-! ## Fibonacci fusion identity

The fusion identity `F(a+b-1) = F(a)*F(b) + F(a-1)*F(b-1)` is derived from
mathlib's `Nat.fib_add` by an index shift. -/

/-- Paper's fusion identity: F(a+b-1) = F(a)*F(b) + F(a-1)*F(b-1) for a, b >= 1.
    Derived from mathlib's Nat.fib_add by index shift.
    lem:pom-fib-fusion-submultiplicativity -/
theorem fib_fusion (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.fib (a + b - 1) = Nat.fib a * Nat.fib b + Nat.fib (a - 1) * Nat.fib (b - 1) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  -- Now a = 1 + a', b = 1 + b'
  -- Goal involves (1 + a'), (1 + b')
  have hsub1 : 1 + a' + (1 + b') - 1 = a' + b' + 1 := by omega
  have hsub2 : 1 + a' - 1 = a' := by omega
  have hsub3 : 1 + b' - 1 = b' := by omega
  rw [hsub1, hsub2, hsub3, Nat.fib_add a' b']
  ring_nf

/-- Strict submultiplicativity: F(a)*F(b) < F(a+b-1) when a >= 2 and b >= 2.
    lem:pom-fib-fusion-submultiplicativity-prod-lt-fusion -/
theorem fib_prod_lt_fib_fusion (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Nat.fib a * Nat.fib b < Nat.fib (a + b - 1) := by
  rw [fib_fusion a b (by omega) (by omega)]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.fib_pos.mpr (by omega))
    (Nat.fib_pos.mpr (by omega)))

/-- F(a+b-1) < F(a+b) when a+b >= 3.
    lem:pom-fib-fusion-submultiplicativity-fusion-lt-sum -/
theorem fib_fusion_lt_fib_sum (a b : Nat) (_ha : 1 ≤ a) (_hb : 1 ≤ b)
    (hab : 3 ≤ a + b) :
    Nat.fib (a + b - 1) < Nat.fib (a + b) := by
  have hab2 : 2 ≤ a + b - 1 := by omega
  have hindex : a + b = (a + b - 1) + 1 := by omega
  rw [hindex]
  exact Nat.fib_lt_fib_succ hab2

/-- Combined: F(a)*F(b) < F(a+b) for a >= 2, b >= 2.
    lem:pom-fib-fusion-submultiplicativity-prod-lt-sum -/
theorem fib_prod_lt_fib_sum (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Nat.fib a * Nat.fib b < Nat.fib (a + b) :=
  Nat.lt_trans (fib_prod_lt_fib_fusion a b ha hb)
    (fib_fusion_lt_fib_sum a b (by omega) (by omega) (by omega))

/-! ## Component fusion gain

The component fusion gain theorem shows that merging two Fibonacci-indexed
components yields a strictly larger Fibonacci number, with a quantified gain. -/

/-- Component fusion gain: F(l+2)*F(l'+2) < F(l+l'+3) for l, l' >= 1.
    cor:pom-fib-component-fusion-gain -/
theorem fib_component_fusion_lt (l l' : Nat) (_hl : 1 ≤ l) (_hl' : 1 ≤ l') :
    Nat.fib (l + 2) * Nat.fib (l' + 2) < Nat.fib (l + l' + 3) := by
  have h : l + l' + 3 = (l + 2) + (l' + 2) - 1 := by omega
  rw [h]
  exact fib_prod_lt_fib_fusion (l + 2) (l' + 2) (by omega) (by omega)

/-- The fusion gain equals F(l+1)*F(l'+1).
    cor:pom-fib-component-fusion-gain-bound -/
theorem fib_component_fusion_gain (l l' : Nat) (_hl : 1 ≤ l) (_hl' : 1 ≤ l') :
    Nat.fib (l + l' + 3) - Nat.fib (l + 2) * Nat.fib (l' + 2) =
      Nat.fib (l + 1) * Nat.fib (l' + 1) := by
  have hfuse := fib_fusion (l + 2) (l' + 2) (by omega) (by omega)
  simp only [show l + 2 - 1 = l + 1 from by omega,
             show l' + 2 - 1 = l' + 1 from by omega] at hfuse
  have h : l + l' + 3 = (l + 2) + (l' + 2) - 1 := by omega
  rw [h, hfuse]
  omega

/-- The fusion gain is at least F(min(l, l') + 1).
    cor:pom-fib-component-fusion-gain-lower -/
theorem fib_component_fusion_gain_lower (l l' : Nat) (hl : 1 ≤ l) (hl' : 1 ≤ l') :
    Nat.fib (min l l' + 1) ≤ Nat.fib (l + 1) * Nat.fib (l' + 1) := by
  rcases Nat.le_total l l' with hll | hll
  · -- min l l' = l
    rw [Nat.min_eq_left hll]
    calc Nat.fib (l + 1)
        = Nat.fib (l + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ Nat.fib (l + 1) * Nat.fib (l' + 1) :=
          Nat.mul_le_mul_left _ (Nat.fib_pos.mpr (by omega))
  · -- min l l' = l'
    rw [Nat.min_eq_right hll]
    calc Nat.fib (l' + 1)
        = 1 * Nat.fib (l' + 1) := (Nat.one_mul _).symm
      _ ≤ Nat.fib (l + 1) * Nat.fib (l' + 1) :=
          Nat.mul_le_mul_right _ (Nat.fib_pos.mpr (by omega))

/-- Combined: the fusion gain F(l+l'+3) - F(l+2)*F(l'+2) is at least F(min(l,l')+1).
    Paper reference: cor:pom-fib-component-fusion-gain (complete form) -/
theorem fib_component_fusion_gain_ge (l l' : Nat) (hl : 1 ≤ l) (hl' : 1 ≤ l') :
    Nat.fib (min l l' + 1) ≤ Nat.fib (l + l' + 3) - Nat.fib (l + 2) * Nat.fib (l' + 2) := by
  rw [fib_component_fusion_gain l l' hl hl']
  exact fib_component_fusion_gain_lower l l' hl hl'

end Omega
