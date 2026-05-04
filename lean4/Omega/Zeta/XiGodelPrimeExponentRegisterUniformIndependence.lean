import Mathlib.Tactic
import Omega.Conclusion.PrimeRegister

namespace Omega.Zeta

open scoped BigOperators

/-- The finite exponent vector as the list consumed by the existing prime Gödel encoder. -/
def xi_godel_prime_exponent_register_uniform_independence_exponent_list
    {n q : ℕ} (v : Fin n → Fin q) : List ℕ :=
  List.ofFn fun i : Fin n => (v i).val

/-- Total-variation envelope on a finite exponent-vector register, without the conventional
factor `1 / 2`; this is the normalization used by the surrounding finite-audit bounds. -/
def xi_godel_prime_exponent_register_uniform_independence_total_variation
    {n q : ℕ} (law productLaw : (Fin n → Fin q) → ℝ) : ℝ :=
  ∑ v, |law v - productLaw v|

/-- Concrete data for transferring a finite decoupling estimate through the prime-exponent
Gödel register. -/
structure xi_godel_prime_exponent_register_uniform_independence_data where
  xi_godel_prime_exponent_register_uniform_independence_register_count : ℕ
  xi_godel_prime_exponent_register_uniform_independence_exponent_bound : ℕ
  xi_godel_prime_exponent_register_uniform_independence_primes : ℕ → ℕ
  xi_godel_prime_exponent_register_uniform_independence_offset : ℕ
  xi_godel_prime_exponent_register_uniform_independence_law :
    (Fin xi_godel_prime_exponent_register_uniform_independence_register_count →
      Fin xi_godel_prime_exponent_register_uniform_independence_exponent_bound) → ℝ
  xi_godel_prime_exponent_register_uniform_independence_product_law :
    (Fin xi_godel_prime_exponent_register_uniform_independence_register_count →
      Fin xi_godel_prime_exponent_register_uniform_independence_exponent_bound) → ℝ
  xi_godel_prime_exponent_register_uniform_independence_epsilon : ℝ
  xi_godel_prime_exponent_register_uniform_independence_pairwise_coprime :
    ∀ i j,
      i ≠ j →
        Nat.Coprime
          (xi_godel_prime_exponent_register_uniform_independence_primes i)
          (xi_godel_prime_exponent_register_uniform_independence_primes j)
  xi_godel_prime_exponent_register_uniform_independence_primes_gt_one :
    ∀ i, 1 < xi_godel_prime_exponent_register_uniform_independence_primes i
  xi_godel_prime_exponent_register_uniform_independence_decoupled_tv_bound :
    xi_godel_prime_exponent_register_uniform_independence_total_variation
        xi_godel_prime_exponent_register_uniform_independence_law
        xi_godel_prime_exponent_register_uniform_independence_product_law ≤
      xi_godel_prime_exponent_register_uniform_independence_epsilon

/-- Prime-product encoding of the bounded exponent vector. -/
def xi_godel_prime_exponent_register_uniform_independence_encoding
    (D : xi_godel_prime_exponent_register_uniform_independence_data)
    (v : Fin D.xi_godel_prime_exponent_register_uniform_independence_register_count →
      Fin D.xi_godel_prime_exponent_register_uniform_independence_exponent_bound) : ℕ :=
  Omega.Conclusion.godelEncoding
    D.xi_godel_prime_exponent_register_uniform_independence_primes
    D.xi_godel_prime_exponent_register_uniform_independence_offset
    (xi_godel_prime_exponent_register_uniform_independence_exponent_list v)

/-- The encoded prime-exponent register keeps the same finite total-variation bound, and the
encoding is injective on fixed-length exponent vectors. -/
def xi_godel_prime_exponent_register_uniform_independence_statement
    (D : xi_godel_prime_exponent_register_uniform_independence_data) : Prop :=
  Function.Injective (xi_godel_prime_exponent_register_uniform_independence_encoding D) ∧
    xi_godel_prime_exponent_register_uniform_independence_total_variation
        D.xi_godel_prime_exponent_register_uniform_independence_law
        D.xi_godel_prime_exponent_register_uniform_independence_product_law ≤
      D.xi_godel_prime_exponent_register_uniform_independence_epsilon

lemma xi_godel_prime_exponent_register_uniform_independence_encoding_injective
    (D : xi_godel_prime_exponent_register_uniform_independence_data) :
    Function.Injective (xi_godel_prime_exponent_register_uniform_independence_encoding D) := by
  intro u v huv
  have hlist :
      xi_godel_prime_exponent_register_uniform_independence_exponent_list u =
        xi_godel_prime_exponent_register_uniform_independence_exponent_list v := by
    apply Omega.Conclusion.godelEncoding_injective_of_eq_length
      D.xi_godel_prime_exponent_register_uniform_independence_primes
      D.xi_godel_prime_exponent_register_uniform_independence_offset
    · simp [xi_godel_prime_exponent_register_uniform_independence_exponent_list]
    · exact D.xi_godel_prime_exponent_register_uniform_independence_pairwise_coprime
    · exact D.xi_godel_prime_exponent_register_uniform_independence_primes_gt_one
    · simpa [xi_godel_prime_exponent_register_uniform_independence_encoding] using huv
  have hnat :
      (fun i => (u i).val) = (fun i => (v i).val) := by
    exact List.ofFn_injective hlist
  funext i
  exact Fin.ext (congrFun hnat i)

/-- Paper label: `cor:xi-godel-prime-exponent-register-uniform-independence`. -/
theorem paper_xi_godel_prime_exponent_register_uniform_independence
    (D : xi_godel_prime_exponent_register_uniform_independence_data) :
    xi_godel_prime_exponent_register_uniform_independence_statement D := by
  exact
    ⟨xi_godel_prime_exponent_register_uniform_independence_encoding_injective D,
      D.xi_godel_prime_exponent_register_uniform_independence_decoupled_tv_bound⟩

end Omega.Zeta
