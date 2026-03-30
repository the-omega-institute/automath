import Omega.Folding.MomentBounds
import Mathlib.Tactic

namespace Omega.Core

/-- The false bit-layer has size `2^(n-1)`.
    thm:discussion-walsh-stokes-higher-flux -/
theorem bit_layer_card_false (n : Nat) (hn : 1 ≤ n) (i : Fin n) :
    ((Finset.univ : Finset (Word n)).filter fun w => w i = false).card = 2 ^ (n - 1) := by
  have hsplit :
      ((Finset.univ : Finset (Word n)).filter fun w => w i = true).card +
      {w ∈ (Finset.univ : Finset (Word n)) | ¬ w i = true}.card = Fintype.card (Word n) := by
    simpa using Finset.filter_card_add_filter_neg_card_eq_card (fun w : Word n => w i = true)
  have htrue := Omega.card_true_at_bit n hn i
  simp only [Bool.eq_true_eq_not_eq_false] at hsplit
  have hcard : Fintype.card (Word n) = 2 ^ n := by simp [Word]
  rw [hcard, htrue] at hsplit
  have hpow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    rw [show n = (n - 1) + 1 from by omega, pow_succ']
    ring
  omega

/-- The true bit-layer has size `2^(n-1)`.
    thm:discussion-walsh-stokes-higher-flux -/
theorem bit_layer_card_true (n : Nat) (hn : 1 ≤ n) (i : Fin n) :
    ((Finset.univ : Finset (Word n)).filter fun w => w i = true).card = 2 ^ (n - 1) := by
  exact Omega.card_true_at_bit n hn i

/-- The two bit-layers have equal cardinality.
    thm:discussion-walsh-stokes-higher-flux -/
theorem bit_layer_card_eq_recovery (n : Nat) (hn : 1 ≤ n) (i : Fin n) :
    ((Finset.univ : Finset (Word n)).filter fun w => w i = false).card =
    ((Finset.univ : Finset (Word n)).filter fun w => w i = true).card := by
  rw [bit_layer_card_false n hn i, bit_layer_card_true n hn i]

end Omega.Core
