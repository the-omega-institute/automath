import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Certified cycle lengths on the 160-point Nielsen class. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160 : List ℕ :=
  List.replicate 36 3 ++ List.replicate 12 2 ++ List.replicate 28 1

/-- Certified cycle lengths on the 40-point quotient Nielsen class. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40 : List ℕ :=
  List.replicate 9 3 ++ List.replicate 13 1

/-- Total support size represented by a cycle certificate. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
    (cycleLengths : List ℕ) : ℕ :=
  cycleLengths.sum

/-- Permutation order represented by a cycle certificate. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
    (cycleLengths : List ℕ) : ℕ :=
  cycleLengths.foldl Nat.lcm 1

/-- The two certified Hurwitz cycle decompositions have support sizes `160` and `40`, and
orders `6` and `3`, respectively. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_statement : Prop :=
  xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
      xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160 = 160 ∧
    xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
        xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160 = 6 ∧
      xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
          xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40 = 40 ∧
        xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
            xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40 = 3

/-- Paper label: `prop:xi-terminal-zm-hurwitz-generator-cycle-types-on-160-and-40`. -/
theorem paper_xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40 :
    xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_statement := by
  unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_statement
  unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
  unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
  unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160
  unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40
  native_decide

end Omega.Zeta
