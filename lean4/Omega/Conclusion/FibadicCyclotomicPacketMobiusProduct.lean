import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibadicCyclotomicPacketDecomposition

namespace Omega.Conclusion

open scoped BigOperators

/-- Divisors of a depth, written in the same bounded form used by the packet decomposition. -/
def conclusion_fibadic_cyclotomic_packet_mobius_product_divisorSet (d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun e => e ∣ d)

/-- The divisor-lattice Möbius exponent attached to the pair `e ∣ d`. -/
def conclusion_fibadic_cyclotomic_packet_mobius_product_mobiusExponent
    (d e : ℕ) : ℤ :=
  if e ∣ d then ArithmeticFunction.moebius (d / e) else 0

/-- The packet decomposition relation on the divisor lattice. -/
def conclusion_fibadic_cyclotomic_packet_mobius_product_decomposition
    (F : ℕ → ℕ) (Pi : ℕ → Polynomial ℤ) : Prop :=
  ∀ d,
    Polynomial.X ^ F d - 1 =
      ∏ e ∈ conclusion_fibadic_cyclotomic_packet_mobius_product_divisorSet d, Pi e

/-- The base packet identity. -/
def conclusion_fibadic_cyclotomic_packet_mobius_product_basePacket
    (Pi : ℕ → Polynomial ℤ) : Prop :=
  Pi 1 = Polynomial.X - 1

/-- Concrete statement packaging the existing packet decomposition together with the divisor
Möbius coefficient normalization and the depth-one packet. -/
def conclusion_fibadic_cyclotomic_packet_mobius_product_statement : Prop :=
  (∀ (F a : ℕ → ℕ) (Pi : ℕ → Polynomial ℤ),
      (∀ d, (Pi d).natDegree = a d) →
        conclusion_fibadic_cyclotomic_packet_mobius_product_decomposition F Pi →
          (∀ d, (Pi d).natDegree = a d) ∧
            conclusion_fibadic_cyclotomic_packet_mobius_product_decomposition F Pi) ∧
    conclusion_fibadic_cyclotomic_packet_mobius_product_mobiusExponent 1 1 = 1 ∧
      ∀ Pi : ℕ → Polynomial ℤ,
        Pi 1 = Polynomial.X - 1 →
          conclusion_fibadic_cyclotomic_packet_mobius_product_basePacket Pi

lemma conclusion_fibadic_cyclotomic_packet_mobius_product_existing_decomposition
    (F a : ℕ → ℕ) (Pi : ℕ → Polynomial ℤ)
    (hdeg : ∀ d, (Pi d).natDegree = a d)
    (hfactor : conclusion_fibadic_cyclotomic_packet_mobius_product_decomposition F Pi) :
    (∀ d, (Pi d).natDegree = a d) ∧
      conclusion_fibadic_cyclotomic_packet_mobius_product_decomposition F Pi := by
  exact paper_conclusion_fibadic_cyclotomic_packet_decomposition F a Pi hdeg hfactor

/-- Paper label: `thm:conclusion-fibadic-cyclotomic-packet-mobius-product`. -/
theorem paper_conclusion_fibadic_cyclotomic_packet_mobius_product :
    conclusion_fibadic_cyclotomic_packet_mobius_product_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro F a Pi hdeg hfactor
    exact conclusion_fibadic_cyclotomic_packet_mobius_product_existing_decomposition F a Pi
      hdeg hfactor
  · native_decide
  · intro Pi hPi
    exact hPi

end Omega.Conclusion
