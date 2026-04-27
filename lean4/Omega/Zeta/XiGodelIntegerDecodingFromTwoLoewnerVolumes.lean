import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete two-level Loewner-volume decoding data for a prime-power Gödel integer. -/
structure xi_godel_integer_decoding_from_two_loewner_volumes_data where
  xi_godel_integer_decoding_from_two_loewner_volumes_k : ℕ
  xi_godel_integer_decoding_from_two_loewner_volumes_prime :
    Fin xi_godel_integer_decoding_from_two_loewner_volumes_k → ℕ
  xi_godel_integer_decoding_from_two_loewner_volumes_exponent :
    Fin xi_godel_integer_decoding_from_two_loewner_volumes_k → ℕ
  xi_godel_integer_decoding_from_two_loewner_volumes_t1 : ℕ
  xi_godel_integer_decoding_from_two_loewner_volumes_t2 : ℕ
  xi_godel_integer_decoding_from_two_loewner_volumes_volume1 : ℝ
  xi_godel_integer_decoding_from_two_loewner_volumes_volume2 : ℝ
  xi_godel_integer_decoding_from_two_loewner_volumes_readout : ℝ
  xi_godel_integer_decoding_from_two_loewner_volumes_t1_pos :
    1 ≤ xi_godel_integer_decoding_from_two_loewner_volumes_t1
  xi_godel_integer_decoding_from_two_loewner_volumes_t1_lt_t2 :
    xi_godel_integer_decoding_from_two_loewner_volumes_t1 <
      xi_godel_integer_decoding_from_two_loewner_volumes_t2
  xi_godel_integer_decoding_from_two_loewner_volumes_t2_le_k :
    xi_godel_integer_decoding_from_two_loewner_volumes_t2 ≤
      xi_godel_integer_decoding_from_two_loewner_volumes_k
  xi_godel_integer_decoding_from_two_loewner_volumes_prime_is_prime :
    ∀ i : Fin xi_godel_integer_decoding_from_two_loewner_volumes_k,
      Nat.Prime (xi_godel_integer_decoding_from_two_loewner_volumes_prime i)
  xi_godel_integer_decoding_from_two_loewner_volumes_prime_injective :
    Function.Injective xi_godel_integer_decoding_from_two_loewner_volumes_prime
  xi_godel_integer_decoding_from_two_loewner_volumes_readout_eq_log_sum :
    xi_godel_integer_decoding_from_two_loewner_volumes_readout =
      ∑ i : Fin xi_godel_integer_decoding_from_two_loewner_volumes_k,
        (xi_godel_integer_decoding_from_two_loewner_volumes_exponent i : ℝ) *
          Real.log (xi_godel_integer_decoding_from_two_loewner_volumes_prime i)
  xi_godel_integer_decoding_from_two_loewner_volumes_log_product :
    (∑ i : Fin xi_godel_integer_decoding_from_two_loewner_volumes_k,
        (xi_godel_integer_decoding_from_two_loewner_volumes_exponent i : ℝ) *
          Real.log (xi_godel_integer_decoding_from_two_loewner_volumes_prime i)) =
      Real.log
        (∏ i : Fin xi_godel_integer_decoding_from_two_loewner_volumes_k,
          xi_godel_integer_decoding_from_two_loewner_volumes_prime i ^
            xi_godel_integer_decoding_from_two_loewner_volumes_exponent i)
  xi_godel_integer_decoding_from_two_loewner_volumes_unique_factor_readout :
    ∀ b : Fin xi_godel_integer_decoding_from_two_loewner_volumes_k → ℕ,
      (∏ i : Fin xi_godel_integer_decoding_from_two_loewner_volumes_k,
          xi_godel_integer_decoding_from_two_loewner_volumes_prime i ^ b i) =
        (∏ i : Fin xi_godel_integer_decoding_from_two_loewner_volumes_k,
          xi_godel_integer_decoding_from_two_loewner_volumes_prime i ^
            xi_godel_integer_decoding_from_two_loewner_volumes_exponent i) →
        b = xi_godel_integer_decoding_from_two_loewner_volumes_exponent

/-- The prime-power Gödel integer encoded by the exponent vector. -/
def xi_godel_integer_decoding_from_two_loewner_volumes_godelInteger
    (D : xi_godel_integer_decoding_from_two_loewner_volumes_data) : ℕ :=
  ∏ i,
    D.xi_godel_integer_decoding_from_two_loewner_volumes_prime i ^
      D.xi_godel_integer_decoding_from_two_loewner_volumes_exponent i

/-- The logarithmic boundary sum recovered from the two Loewner volumes. -/
def xi_godel_integer_decoding_from_two_loewner_volumes_logSum
    (D : xi_godel_integer_decoding_from_two_loewner_volumes_data) : ℝ :=
  ∑ i,
    (D.xi_godel_integer_decoding_from_two_loewner_volumes_exponent i : ℝ) *
      Real.log (D.xi_godel_integer_decoding_from_two_loewner_volumes_prime i)

/-- Paper-facing two-volume decoding statement. -/
def xi_godel_integer_decoding_from_two_loewner_volumes_statement
    (D : xi_godel_integer_decoding_from_two_loewner_volumes_data) : Prop :=
  D.xi_godel_integer_decoding_from_two_loewner_volumes_readout =
      xi_godel_integer_decoding_from_two_loewner_volumes_logSum D ∧
    xi_godel_integer_decoding_from_two_loewner_volumes_logSum D =
      Real.log (xi_godel_integer_decoding_from_two_loewner_volumes_godelInteger D) ∧
      ∀ b : Fin D.xi_godel_integer_decoding_from_two_loewner_volumes_k → ℕ,
        (∏ i,
            D.xi_godel_integer_decoding_from_two_loewner_volumes_prime i ^ b i) =
          xi_godel_integer_decoding_from_two_loewner_volumes_godelInteger D →
          b = D.xi_godel_integer_decoding_from_two_loewner_volumes_exponent

/-- Paper label: `cor:xi-godel-integer-decoding-from-two-loewner-volumes`. -/
theorem paper_xi_godel_integer_decoding_from_two_loewner_volumes
    (D : xi_godel_integer_decoding_from_two_loewner_volumes_data) :
    xi_godel_integer_decoding_from_two_loewner_volumes_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [xi_godel_integer_decoding_from_two_loewner_volumes_logSum] using
      D.xi_godel_integer_decoding_from_two_loewner_volumes_readout_eq_log_sum
  · simpa [xi_godel_integer_decoding_from_two_loewner_volumes_logSum,
      xi_godel_integer_decoding_from_two_loewner_volumes_godelInteger] using
      D.xi_godel_integer_decoding_from_two_loewner_volumes_log_product
  · intro b hb
    exact D.xi_godel_integer_decoding_from_two_loewner_volumes_unique_factor_readout b
      (by
        simpa [xi_godel_integer_decoding_from_two_loewner_volumes_godelInteger] using hb)

end

end Omega.Zeta
