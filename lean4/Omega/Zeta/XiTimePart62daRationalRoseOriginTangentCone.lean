import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Omega.Zeta

/-- The zero preimages of the rose are represented by the `2n` odd half-periods. -/
abbrev xi_time_part62da_rational_rose_origin_tangent_cone_zero_preimages (n : ℕ) :=
  Fin (2 * n)

/-- Tangent directions at the origin, reduced modulo the unoriented angle period. -/
def xi_time_part62da_rational_rose_origin_tangent_cone_direction (d n : ℕ) (k : Fin n) :
    Fin n :=
  ⟨(d * k.val) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) k.isLt)⟩

/-- The finite tangent cone direction set of the rational rose at the origin. -/
def xi_time_part62da_rational_rose_origin_tangent_cone_directions (d n : ℕ) : Finset (Fin n) :=
  Finset.univ.image (xi_time_part62da_rational_rose_origin_tangent_cone_direction d n)

lemma xi_time_part62da_rational_rose_origin_tangent_cone_direction_injective
    {d n : ℕ} (hcop : Nat.Coprime d n) :
    Function.Injective (xi_time_part62da_rational_rose_origin_tangent_cone_direction d n) := by
  intro a b h
  have hval :
      (d * a.val) % n = (d * b.val) % n := by
    exact congrArg Fin.val h
  have hmod : d * a.val ≡ d * b.val [MOD n] := hval
  have hgcd : Nat.gcd n d = 1 := by
    rw [Nat.gcd_comm]
    exact hcop
  have hab : a.val ≡ b.val [MOD n] :=
    Nat.ModEq.cancel_left_of_coprime hgcd hmod
  change a.val % n = b.val % n at hab
  rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hab
  exact Fin.ext hab

lemma xi_time_part62da_rational_rose_origin_tangent_cone_direction_card
    {d n : ℕ} (hcop : Nat.Coprime d n) :
    (xi_time_part62da_rational_rose_origin_tangent_cone_directions d n).card = n := by
  rw [xi_time_part62da_rational_rose_origin_tangent_cone_directions]
  rw [Finset.card_image_of_injective _
    (xi_time_part62da_rational_rose_origin_tangent_cone_direction_injective hcop)]
  simp

lemma xi_time_part62da_rational_rose_origin_tangent_cone_branch_pair_criterion
    {d n k k' : ℕ} (hcop : Nat.Coprime d n) :
    d * k ≡ d * k' [MOD n] ↔ k ≡ k' [MOD n] := by
  constructor
  · intro h
    have hgcd : Nat.gcd n d = 1 := by
      rw [Nat.gcd_comm]
      exact hcop
    exact Nat.ModEq.cancel_left_of_coprime hgcd h
  · intro h
    exact h.mul_left d

/-- Concrete arithmetic statement for the tangent cone of the coprime rational rose. -/
def xi_time_part62da_rational_rose_origin_tangent_cone_statement : Prop :=
  ∀ d n : ℕ, Nat.Coprime d n → 0 < n → n < d →
    Fintype.card (xi_time_part62da_rational_rose_origin_tangent_cone_zero_preimages n) =
        2 * n ∧
      (xi_time_part62da_rational_rose_origin_tangent_cone_directions d n).card = n ∧
      (∀ k k' : ℕ,
        d * k ≡ d * k' [MOD n] ↔ k ≡ k' [MOD n])

/-- Paper label: `prop:xi-time-part62da-rational-rose-origin-tangent-cone`. -/
theorem paper_xi_time_part62da_rational_rose_origin_tangent_cone :
    xi_time_part62da_rational_rose_origin_tangent_cone_statement := by
  intro d n hcop hn hnd
  exact ⟨by simp [xi_time_part62da_rational_rose_origin_tangent_cone_zero_preimages],
    xi_time_part62da_rational_rose_origin_tangent_cone_direction_card hcop,
    fun k k' =>
      xi_time_part62da_rational_rose_origin_tangent_cone_branch_pair_criterion hcop⟩

end Omega.Zeta
