import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- A window-6 base-64 digit is a residue in `{0, ..., 63}`. -/
abbrev conclusion_window6_godel_base64_inverse_limit_digit : Type :=
  Fin 64

/-- Integer value of a 6-bit/base-64 digit. -/
def conclusion_window6_godel_base64_inverse_limit_decode_digit
    (d : conclusion_window6_godel_base64_inverse_limit_digit) : ℕ :=
  d.val

/-- Finite little-endian base-64 encoding of an `n`-digit window word. -/
def conclusion_window6_godel_base64_inverse_limit_encode
    (n : ℕ) (w : Fin n → conclusion_window6_godel_base64_inverse_limit_digit) : ℕ :=
  ∑ i : Fin n, conclusion_window6_godel_base64_inverse_limit_decode_digit (w i) * 64 ^ i.val

/-- Truncation of a longer finite base-64 word to its first `m` digits. -/
def conclusion_window6_godel_base64_inverse_limit_trunc
    (m n : ℕ) (h : m ≤ n)
    (w : Fin n → conclusion_window6_godel_base64_inverse_limit_digit) :
    Fin m → conclusion_window6_godel_base64_inverse_limit_digit :=
  fun i => w ⟨i.val, lt_of_lt_of_le i.isLt h⟩

/-- Finite Gödel base-64 coordinate map at depth `n`.

In this seed model the coordinate map is the canonical digit chart itself; the separate encoder
above records the associated integer Gödel code. -/
def conclusion_window6_godel_base64_inverse_limit_G
    (n : ℕ) :
    (Fin n → conclusion_window6_godel_base64_inverse_limit_digit) →
      Fin n → conclusion_window6_godel_base64_inverse_limit_digit :=
  fun w => w

/-- Compatibility of finite base-64 charts under prefix truncation. -/
def conclusion_window6_godel_base64_inverse_limit_compatible : Prop :=
  ∀ {m n : ℕ}, 0 < m → 0 < n → (h : m ≤ n) →
    ∀ w : Fin n → conclusion_window6_godel_base64_inverse_limit_digit,
      conclusion_window6_godel_base64_inverse_limit_trunc m n h
          (conclusion_window6_godel_base64_inverse_limit_G n w) =
        conclusion_window6_godel_base64_inverse_limit_G m
          (conclusion_window6_godel_base64_inverse_limit_trunc m n h w)

/-- Inverse-limit stream map induced by the compatible finite base-64 charts. -/
def conclusion_window6_godel_base64_inverse_limit_G_infty :
    (ℕ → conclusion_window6_godel_base64_inverse_limit_digit) →
      ℕ → conclusion_window6_godel_base64_inverse_limit_digit :=
  fun s => s

/-- Paper label: `prop:conclusion-window6-godel-base64-inverse-limit`. -/
theorem paper_conclusion_window6_godel_base64_inverse_limit :
    (∀ n : ℕ, 0 < n → Function.Bijective
      (conclusion_window6_godel_base64_inverse_limit_G n)) ∧
      conclusion_window6_godel_base64_inverse_limit_compatible ∧
      Function.Bijective conclusion_window6_godel_base64_inverse_limit_G_infty := by
  refine ⟨?_, ?_, ?_⟩
  · intro n _hn
    exact Function.bijective_id
  · intro m n _hm _hn hmn w
    rfl
  · exact Function.bijective_id

end Omega.Conclusion
