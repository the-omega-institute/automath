import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Eventual-halting bit stream: `none` is the nonhalting case, and `some N` is the first
halting time with all later bits equal to one. -/
def conclusion_halting_alpha_algebraic_form_bit (haltTime : Option ℕ) (n : ℕ) : ℤ :=
  match haltTime with
  | none => 0
  | some N => if N ≤ n then 1 else 0

/-- The finite prefix scalar read from the first `m` simulated bits. -/
def conclusion_halting_alpha_algebraic_form_prefix (B m : ℕ) (t : ℕ → ℤ) : ℤ :=
  Finset.sum (Finset.range m) fun n => t n * (B : ℤ) ^ n

/-- The finite prefix residue modulo `B^m`. -/
def conclusion_halting_alpha_algebraic_form_prefix_residue (B m : ℕ) (t : ℕ → ℤ) : ℤ :=
  conclusion_halting_alpha_algebraic_form_prefix B m t % (B : ℤ) ^ m

/-- The formal `B`-adic scalar attached to the eventual-halting stream. -/
def conclusion_halting_alpha_algebraic_form_alpha (B : ℕ) (haltTime : Option ℕ) : ℤ :=
  match haltTime with
  | none => 0
  | some N => -((B : ℤ) ^ N)

/-- Concrete algebraic-form statement for the eventual-halting scalar and finite-prefix residues. -/
def conclusion_halting_alpha_algebraic_form_statement : Prop :=
  (∀ B : ℕ, conclusion_halting_alpha_algebraic_form_alpha B none = 0) ∧
    (∀ B N : ℕ,
      2 ≤ B →
        conclusion_halting_alpha_algebraic_form_alpha B (some N) = -((B : ℤ) ^ N) ∧
          conclusion_halting_alpha_algebraic_form_alpha B (some N) ≠ 0) ∧
    (∀ (B m : ℕ) (t u : ℕ → ℤ),
      (∀ n, n < m → t n = u n) →
        conclusion_halting_alpha_algebraic_form_prefix_residue B m t =
          conclusion_halting_alpha_algebraic_form_prefix_residue B m u)

theorem conclusion_halting_alpha_algebraic_form_prefix_eq_of_agree
    {B m : ℕ} {t u : ℕ → ℤ} (h : ∀ n, n < m → t n = u n) :
    conclusion_halting_alpha_algebraic_form_prefix B m t =
      conclusion_halting_alpha_algebraic_form_prefix B m u := by
  unfold conclusion_halting_alpha_algebraic_form_prefix
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n (Finset.mem_range.mp hn)]

/-- Paper label: `lem:conclusion-halting-alpha-algebraic-form`. -/
theorem paper_conclusion_halting_alpha_algebraic_form :
    conclusion_halting_alpha_algebraic_form_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro B
    rfl
  · intro B N hB
    constructor
    · rfl
    · have hBpos : (0 : ℤ) < B := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hB)
      have hpow_pos : (0 : ℤ) < (B : ℤ) ^ N := pow_pos hBpos N
      exact neg_ne_zero.mpr hpow_pos.ne'
  · intro B m t u h
    unfold conclusion_halting_alpha_algebraic_form_prefix_residue
    rw [conclusion_halting_alpha_algebraic_form_prefix_eq_of_agree h]

end Omega.Conclusion
