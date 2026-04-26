import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Base-`B` value of a little-endian digit list. -/
def conclusion_godel_leyang_prefix_congruence_equivalence_value (B : ℕ) (xs : List ℕ) : ℕ :=
  Nat.ofDigits B xs

/-- Agreement of the first `n` digits. -/
def conclusion_godel_leyang_prefix_congruence_equivalence_prefix_agree
    (n : ℕ) (xs ys : List ℕ) : Prop :=
  List.take n xs = List.take n ys

/-- Paper label: `prop:conclusion-godel-leyang-prefix-congruence-equivalence`. For concrete
finite base-`B` digit strings, agreement of the first `n` digits is equivalent to congruence
modulo `B ^ n`. -/
theorem paper_conclusion_godel_leyang_prefix_congruence_equivalence
    {B n : ℕ} (hB : 2 ≤ B) {xs ys : List ℕ}
    (hxs : ∀ z ∈ xs, z < B) (hys : ∀ z ∈ ys, z < B)
    (hlenx : n ≤ xs.length) (hleny : n ≤ ys.length) :
    conclusion_godel_leyang_prefix_congruence_equivalence_prefix_agree n xs ys ↔
      conclusion_godel_leyang_prefix_congruence_equivalence_value B xs ≡
        conclusion_godel_leyang_prefix_congruence_equivalence_value B ys [MOD B ^ n] := by
  constructor
  · intro hprefix
    rw [Nat.ModEq]
    rw [conclusion_godel_leyang_prefix_congruence_equivalence_value,
      conclusion_godel_leyang_prefix_congruence_equivalence_value,
      Nat.ofDigits_mod_pow_eq_ofDigits_take n (Nat.zero_lt_of_lt hB) xs hxs,
      Nat.ofDigits_mod_pow_eq_ofDigits_take n (Nat.zero_lt_of_lt hB) ys hys]
    exact congrArg (Nat.ofDigits B) hprefix
  · intro hcongr
    rw [Nat.ModEq] at hcongr
    rw [conclusion_godel_leyang_prefix_congruence_equivalence_value,
      conclusion_godel_leyang_prefix_congruence_equivalence_value,
      Nat.ofDigits_mod_pow_eq_ofDigits_take n (Nat.zero_lt_of_lt hB) xs hxs,
      Nat.ofDigits_mod_pow_eq_ofDigits_take n (Nat.zero_lt_of_lt hB) ys hys] at hcongr
    have hx :
        Nat.ofDigits B (List.take n xs) = Nat.ofDigits B (List.take n ys) := by
      exact hcongr
    have htake_len : (List.take n xs).length = (List.take n ys).length := by
      simp [List.length_take, hlenx, hleny]
    have htake_xs : ∀ z ∈ List.take n xs, z < B := by
      intro z hz
      exact hxs z (List.mem_of_mem_take hz)
    have htake_ys : ∀ z ∈ List.take n ys, z < B := by
      intro z hz
      exact hys z (List.mem_of_mem_take hz)
    exact Nat.ofDigits_inj_of_len_eq (Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨by omega, by omega⟩)
      htake_len htake_xs htake_ys hx

end Omega.Conclusion
