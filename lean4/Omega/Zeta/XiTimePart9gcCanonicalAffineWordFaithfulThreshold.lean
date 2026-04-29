import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- Variable-length words with digits bounded by `M`. -/
def xi_time_part9gc_canonical_affine_word_faithful_threshold_word (M : ℕ) : Type :=
  { l : List ℕ // ∀ d ∈ l, d ≤ M }

/-- The canonical affine word value: length multiplier and little-endian digit polynomial. -/
def xi_time_part9gc_canonical_affine_word_faithful_threshold_value (C M : ℕ) :
    xi_time_part9gc_canonical_affine_word_faithful_threshold_word M → ℕ × ℕ :=
  fun w => (C ^ w.1.length, Nat.ofDigits C w.1)

/-- Paper label: `thm:xi-time-part9gc-canonical-affine-word-faithful-threshold`. -/
theorem paper_xi_time_part9gc_canonical_affine_word_faithful_threshold (C M : ℕ)
    (hC : 2 ≤ C) :
    Function.Injective (xi_time_part9gc_canonical_affine_word_faithful_threshold_value C M) ↔
      M < C := by
  constructor
  · intro hinj
    by_contra hnot
    have hCM : C ≤ M := Nat.le_of_not_gt hnot
    have hM1 : 1 ≤ M := by omega
    let wC0 : xi_time_part9gc_canonical_affine_word_faithful_threshold_word M :=
      ⟨[C, 0], by
        intro d hd
        simp at hd
        omega⟩
    let w01 : xi_time_part9gc_canonical_affine_word_faithful_threshold_word M :=
      ⟨[0, 1], by
        intro d hd
        simp at hd
        omega⟩
    have hval :
        xi_time_part9gc_canonical_affine_word_faithful_threshold_value C M wC0 =
          xi_time_part9gc_canonical_affine_word_faithful_threshold_value C M w01 := by
      simp [xi_time_part9gc_canonical_affine_word_faithful_threshold_value, wC0, w01,
        Nat.ofDigits]
    have hword := hinj hval
    have hlist : [C, 0] = [0, 1] := congrArg Subtype.val hword
    have hC0 : C = 0 := by
      injection hlist
    omega
  · intro hMC
    rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ hval
    have hlenPow : C ^ l₁.length = C ^ l₂.length := congrArg Prod.fst hval
    have hlen : l₁.length = l₂.length := Nat.pow_right_injective hC hlenPow
    have hd₁ : ∀ d ∈ l₁, d < C := fun d hd => lt_of_le_of_lt (hl₁ d hd) hMC
    have hd₂ : ∀ d ∈ l₂, d < C := fun d hd => lt_of_le_of_lt (hl₂ d hd) hMC
    have hdigits : Nat.ofDigits C l₁ = Nat.ofDigits C l₂ := congrArg Prod.snd hval
    have hlists : l₁ = l₂ :=
      Nat.ofDigits_inj_of_len_eq (lt_of_lt_of_le Nat.one_lt_two hC) hlen hd₁ hd₂ hdigits
    exact Subtype.ext hlists

end Omega.Zeta
