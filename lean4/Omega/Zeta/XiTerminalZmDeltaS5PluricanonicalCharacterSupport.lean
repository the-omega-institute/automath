import Mathlib.Tactic

namespace Omega.Zeta

/-- The four conjugacy-class buckets relevant to the terminal `S₅` pluricanonical character
calculation: identity, transpositions, five-cycles, and all remaining classes. -/
inductive xi_terminal_zm_delta_s5_pluricanonical_character_support_Class where
  | xi_terminal_zm_delta_s5_pluricanonical_character_support_identity
  | xi_terminal_zm_delta_s5_pluricanonical_character_support_transposition
  | xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycle
  | xi_terminal_zm_delta_s5_pluricanonical_character_support_other
  deriving DecidableEq, Fintype

/-- The periodic five-cycle contribution
`∑_{k=1}^4 ζ₅^{kn}/(1-ζ₅^k)`, represented by its exact residue table. -/
def xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycleValue
    (n : Nat) : ℤ :=
  match n % 5 with
  | 0 => 2
  | 1 => -2
  | 2 => -1
  | 3 => 0
  | _ => 1

/-- The finite class-function table for the pluricanonical character `χₙ`. -/
def xi_terminal_zm_delta_s5_pluricanonical_character_support_character
    (n : Nat)
    (C : xi_terminal_zm_delta_s5_pluricanonical_character_support_Class) : ℤ :=
  match C with
  | .xi_terminal_zm_delta_s5_pluricanonical_character_support_identity =>
      108 * (2 * (n : ℤ) - 1)
  | .xi_terminal_zm_delta_s5_pluricanonical_character_support_transposition =>
      18 * (-1 : ℤ) ^ n
  | .xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycle =>
      xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycleValue n
  | .xi_terminal_zm_delta_s5_pluricanonical_character_support_other => 0

/-- Concrete statement for the support and residue-periodic value table of the terminal `S₅`
pluricanonical character. -/
def xi_terminal_zm_delta_s5_pluricanonical_character_support_statement (n : Nat) : Prop :=
  2 <= n ∧
    (∀ C, xi_terminal_zm_delta_s5_pluricanonical_character_support_character n C ≠ 0 →
      C = .xi_terminal_zm_delta_s5_pluricanonical_character_support_identity ∨
        C = .xi_terminal_zm_delta_s5_pluricanonical_character_support_transposition ∨
        C = .xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycle) ∧
    xi_terminal_zm_delta_s5_pluricanonical_character_support_character n
        .xi_terminal_zm_delta_s5_pluricanonical_character_support_identity =
      108 * (2 * (n : ℤ) - 1) ∧
    xi_terminal_zm_delta_s5_pluricanonical_character_support_character n
        .xi_terminal_zm_delta_s5_pluricanonical_character_support_transposition =
      18 * (-1 : ℤ) ^ n ∧
    xi_terminal_zm_delta_s5_pluricanonical_character_support_character n
        .xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycle =
      xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycleValue n ∧
    xi_terminal_zm_delta_s5_pluricanonical_character_support_character n
        .xi_terminal_zm_delta_s5_pluricanonical_character_support_other = 0 ∧
    xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycleValue n =
      (match n % 5 with
      | 0 => 2
      | 1 => -2
      | 2 => -1
      | 3 => 0
      | _ => 1) ∧
    ∀ m, m % 5 = n % 5 →
      xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycleValue m =
        xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycleValue n

/-- Paper label: `thm:xi-terminal-zm-delta-s5-pluricanonical-character-support`. -/
theorem paper_xi_terminal_zm_delta_s5_pluricanonical_character_support
    (n : Nat) (hn : 2 <= n) :
    xi_terminal_zm_delta_s5_pluricanonical_character_support_statement n := by
  refine ⟨hn, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro C hC
    cases C with
    | xi_terminal_zm_delta_s5_pluricanonical_character_support_identity => exact Or.inl rfl
    | xi_terminal_zm_delta_s5_pluricanonical_character_support_transposition =>
        exact Or.inr (Or.inl rfl)
    | xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycle =>
        exact Or.inr (Or.inr rfl)
    | xi_terminal_zm_delta_s5_pluricanonical_character_support_other =>
        simp [xi_terminal_zm_delta_s5_pluricanonical_character_support_character] at hC
  · intro m hm
    simp [xi_terminal_zm_delta_s5_pluricanonical_character_support_fiveCycleValue, hm]

end Omega.Zeta
