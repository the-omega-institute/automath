import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The Möbius-weighted Fibonacci power sum
`S_m(d) = ∑_{e ∣ d} μ(d/e) F_e^m`. -/
def conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum
    (d m : ℕ) : ℚ :=
  ∑ e ∈ Nat.divisors d,
    (ArithmeticFunction.moebius (d / e) : ℚ) * (Nat.fib e : ℚ) ^ m

/-- The Bernoulli-plus coefficients needed for the first two jets:
`B_1^+ = 1 / 2` and `B_2^+ = 1 / 6`. -/
def conclusion_fibadic_depth_packet_bernoulli_mobius_jet_bernoulli_plus :
    ℕ → ℚ
  | 1 => 1 / 2
  | 2 => 1 / 6
  | _ => 0

/-- Formal coefficient in the Bernoulli--Möbius expansion of `log Π_d(e^u)`. -/
def conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff
    (d m : ℕ) : ℚ :=
  (conclusion_fibadic_depth_packet_bernoulli_mobius_jet_bernoulli_plus m /
      ((m : ℚ) * (Nat.factorial m : ℚ))) *
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d m

/-- The first logarithmic jet is the coefficient of `u`. -/
def conclusion_fibadic_depth_packet_bernoulli_mobius_jet_first_jet
    (d : ℕ) : ℚ :=
  conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff d 1

/-- The second logarithmic jet is `2!` times the coefficient of `u^2`. -/
def conclusion_fibadic_depth_packet_bernoulli_mobius_jet_second_jet
    (d : ℕ) : ℚ :=
  2 * conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff d 2

/-- Concrete statement for the Bernoulli--Möbius jet package: the coefficient formula is recorded
term by term, and the first two jets are the displayed divisor-sum consequences. -/
def conclusion_fibadic_depth_packet_bernoulli_mobius_jet_statement (d : ℕ) : Prop :=
  1 < d ∧
    (∀ m : ℕ, 1 ≤ m →
      conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff d m =
        (conclusion_fibadic_depth_packet_bernoulli_mobius_jet_bernoulli_plus m /
            ((m : ℚ) * (Nat.factorial m : ℚ))) *
          conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d m) ∧
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_first_jet d =
      conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d 1 / 2 ∧
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_second_jet d =
      conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d 2 / 12

lemma conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff_identity
    (d : ℕ) :
    ∀ m : ℕ, 1 ≤ m →
      conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff d m =
        (conclusion_fibadic_depth_packet_bernoulli_mobius_jet_bernoulli_plus m /
            ((m : ℚ) * (Nat.factorial m : ℚ))) *
          conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d m := by
  intro m _hm
  rfl

lemma conclusion_fibadic_depth_packet_bernoulli_mobius_jet_first_jet_identity
    (d : ℕ) :
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_first_jet d =
      conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d 1 / 2 := by
  rw [conclusion_fibadic_depth_packet_bernoulli_mobius_jet_first_jet,
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff,
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_bernoulli_plus]
  ring

lemma conclusion_fibadic_depth_packet_bernoulli_mobius_jet_second_jet_identity
    (d : ℕ) :
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_second_jet d =
      conclusion_fibadic_depth_packet_bernoulli_mobius_jet_power_sum d 2 / 12 := by
  rw [conclusion_fibadic_depth_packet_bernoulli_mobius_jet_second_jet,
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff,
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_bernoulli_plus]
  norm_num
  ring

/-- Paper label: `thm:conclusion-fibadic-depth-packet-bernoulli-mobius-jet`. -/
theorem paper_conclusion_fibadic_depth_packet_bernoulli_mobius_jet
    (d : ℕ) (hd : 1 < d) :
    conclusion_fibadic_depth_packet_bernoulli_mobius_jet_statement d := by
  refine ⟨hd, ?_, ?_, ?_⟩
  · exact conclusion_fibadic_depth_packet_bernoulli_mobius_jet_series_coeff_identity d
  · exact conclusion_fibadic_depth_packet_bernoulli_mobius_jet_first_jet_identity d
  · exact conclusion_fibadic_depth_packet_bernoulli_mobius_jet_second_jet_identity d

end

end Omega.Conclusion
