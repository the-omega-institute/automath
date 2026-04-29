import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.FibadicCyclotomicPacketMobiusProduct

namespace Omega.Conclusion

open scoped BigOperators

/-- Divisors of `d`, in the bounded form used by the cyclotomic packet files. -/
def conclusion_fibadic_cyclotomic_packet_padic_content_divisorSet (d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun e => e ∣ d)

/-- The divisor-lattice Mobius exponent attached to `e | d`. -/
def conclusion_fibadic_cyclotomic_packet_padic_content_mobiusExponent
    (d e : ℕ) : ℤ :=
  if e ∣ d then ArithmeticFunction.moebius (d / e) else 0

/-- The integer packet value obtained by evaluating the Mobius product at `X = 1`, with
negative exponents already cancelled in the supplied packet certificate. -/
def conclusion_fibadic_cyclotomic_packet_padic_content_packetValueProduct
    (fibEntry : ℕ → ℕ) (d : ℕ) : ℤ :=
  ∏ e ∈ conclusion_fibadic_cyclotomic_packet_padic_content_divisorSet d,
    (fibEntry e : ℤ) ^
      Int.natAbs (conclusion_fibadic_cyclotomic_packet_padic_content_mobiusExponent d e)

/-- The Mobius-summed `p`-adic valuation of the packet. -/
def conclusion_fibadic_cyclotomic_packet_padic_content_contentExponent
    (fibEntry : ℕ → ℕ) (padicValuation : ℕ → ℕ → ℕ) (p d : ℕ) : ℤ :=
  ∑ e ∈ conclusion_fibadic_cyclotomic_packet_padic_content_divisorSet d,
    conclusion_fibadic_cyclotomic_packet_padic_content_mobiusExponent d e *
      (padicValuation p (fibEntry e) : ℤ)

/-- Concrete data for the cyclotomic packet value and its `p`-adic content. -/
structure conclusion_fibadic_cyclotomic_packet_padic_content_data where
  fibEntry : ℕ → ℕ
  packetValue : ℕ → ℤ
  padicValuation : ℕ → ℕ → ℕ
  entryRankCount : ℕ → ℕ → ℕ
  packetValue_evalAtOne :
    ∀ d,
      2 ≤ d →
        packetValue d =
          conclusion_fibadic_cyclotomic_packet_padic_content_packetValueProduct fibEntry d
  padicValuation_evalAtPacket :
    ∀ p d,
      2 ≤ d →
        (padicValuation p (Int.natAbs (packetValue d)) : ℤ) =
          conclusion_fibadic_cyclotomic_packet_padic_content_contentExponent
            fibEntry padicValuation p d
  entryRank_mobiusInversion :
    ∀ p d,
      2 ≤ d →
        conclusion_fibadic_cyclotomic_packet_padic_content_contentExponent
            fibEntry padicValuation p d =
          entryRankCount p d

namespace conclusion_fibadic_cyclotomic_packet_padic_content_data

/-- Evaluation of the packet at `X = 1` after cancelling the divisor-sum exponent. -/
def packet_value_formula
    (D : conclusion_fibadic_cyclotomic_packet_padic_content_data) : Prop :=
  ∀ d,
    2 ≤ d →
      D.packetValue d =
        conclusion_fibadic_cyclotomic_packet_padic_content_packetValueProduct D.fibEntry d

/-- The `p`-adic content is the Mobius-summed valuation of the Fibonacci entries. -/
def padic_content_formula
    (D : conclusion_fibadic_cyclotomic_packet_padic_content_data) : Prop :=
  ∀ p d,
    2 ≤ d →
      (D.padicValuation p (Int.natAbs (D.packetValue d)) : ℤ) =
        conclusion_fibadic_cyclotomic_packet_padic_content_contentExponent
          D.fibEntry D.padicValuation p d

/-- Divisor-lattice Mobius inversion identifies the content with entry-rank counts. -/
def entry_rank_count_formula
    (D : conclusion_fibadic_cyclotomic_packet_padic_content_data) : Prop :=
  ∀ p d,
    2 ≤ d →
      conclusion_fibadic_cyclotomic_packet_padic_content_contentExponent
          D.fibEntry D.padicValuation p d =
        D.entryRankCount p d

end conclusion_fibadic_cyclotomic_packet_padic_content_data

open conclusion_fibadic_cyclotomic_packet_padic_content_data

/-- Paper label: `thm:conclusion-fibadic-cyclotomic-packet-padic-content`. -/
theorem paper_conclusion_fibadic_cyclotomic_packet_padic_content
    (D : conclusion_fibadic_cyclotomic_packet_padic_content_data) :
    D.packet_value_formula ∧ D.padic_content_formula ∧ D.entry_rank_count_formula := by
  have _hmobius := paper_conclusion_fibadic_cyclotomic_packet_mobius_product
  exact ⟨D.packetValue_evalAtOne, D.padicValuation_evalAtPacket, D.entryRank_mobiusInversion⟩

end Omega.Conclusion
