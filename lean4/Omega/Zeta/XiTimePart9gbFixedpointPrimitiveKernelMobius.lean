import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Words of length `k` over an alphabet with `alphabet` letters. -/
abbrev xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word
    (alphabet k : Nat) : Type :=
  Fin k -> Fin alphabet

/-- Periodic extension of a nonempty finite word. -/
def xi_time_part9gb_fixedpoint_primitive_kernel_mobius_periodicDigit
    {alphabet k : Nat} (hk : 0 < k)
    (w : xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word alphabet k)
    (n : Nat) : Fin alphabet :=
  w ⟨n % k, Nat.mod_lt n hk⟩

/-- The unary primitive layer: the unique unary word is primitive exactly in period `1`. -/
def xi_time_part9gb_fixedpoint_primitive_kernel_mobius_unaryPrimitiveCount
    (k : Nat) : Nat :=
  if k = 1 then 1 else 0

/-- Concrete audited core for the fixed-point primitive-kernel/Mobius theorem.

For the one-letter alphabet all finite words determine the same periodic stream, the layer
count is one, and the divisor decomposition has the expected primitive kernel concentrated
in period `1`. -/
def xi_time_part9gb_fixedpoint_primitive_kernel_mobius_statement : Prop :=
  (∀ k : Nat, Fintype.card
      (xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word 1 k) = 1) ∧
    (∀ {k l : Nat} (hk : 0 < k) (hl : 0 < l)
        (a : xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word 1 k)
        (b : xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word 1 l),
      ∀ n : Nat,
        xi_time_part9gb_fixedpoint_primitive_kernel_mobius_periodicDigit hk a n =
          xi_time_part9gb_fixedpoint_primitive_kernel_mobius_periodicDigit hl b n) ∧
    (∀ k : Nat, 0 < k →
      Finset.sum k.divisors
          (fun d => xi_time_part9gb_fixedpoint_primitive_kernel_mobius_unaryPrimitiveCount d) =
        Fintype.card (xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word 1 k))

/-- Paper label: `thm:xi-time-part9gb-fixedpoint-primitive-kernel-mobius`. -/
theorem paper_xi_time_part9gb_fixedpoint_primitive_kernel_mobius :
    xi_time_part9gb_fixedpoint_primitive_kernel_mobius_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp [xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word]
  · intro k l hk hl a b n
    exact Subsingleton.elim _ _
  · intro k hk
    rw [show Fintype.card
        (xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word 1 k) = 1 by
      simp [xi_time_part9gb_fixedpoint_primitive_kernel_mobius_word]]
    simp only [xi_time_part9gb_fixedpoint_primitive_kernel_mobius_unaryPrimitiveCount]
    rw [Finset.sum_ite_eq']
    simp [Nat.mem_divisors, Nat.ne_of_gt hk]

end Omega.Zeta
