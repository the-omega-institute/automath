import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The `i`th prime-register logarithmic weight. -/
noncomputable def xi_chain_interior_canonical_arithmeticization_optimal_order_primeLogWeight
    (i : ℕ) : ℝ :=
  Real.log (Nat.nth Nat.Prime i)

/-- Canonical Boolean prime-register code: selected coordinates contribute their prime factor. -/
noncomputable def xi_chain_interior_canonical_arithmeticization_optimal_order_primeRegisterCode
    (n : ℕ) (bits : Fin n → Bool) : ℕ :=
  ∏ i : Fin n, if bits i then Nat.nth Nat.Prime i.val else 1

/-- Logarithmic size of the canonical Boolean prime-register code. -/
noncomputable def xi_chain_interior_canonical_arithmeticization_optimal_order_logCode
    (n : ℕ) (bits : Fin n → Bool) : ℝ :=
  ∑ i : Fin n,
    if bits i then
      xi_chain_interior_canonical_arithmeticization_optimal_order_primeLogWeight i.val
    else
      0

/-- The all-ones Boolean register, which realizes the worst-case code length. -/
def xi_chain_interior_canonical_arithmeticization_optimal_order_allOnes
    (n : ℕ) : Fin n → Bool :=
  fun _ => true

/-- Sum of logarithmic weights over the first `n` prime-register coordinates. -/
noncomputable def xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes
    (n : ℕ) : ℝ :=
  xi_chain_interior_canonical_arithmeticization_optimal_order_logCode n
    (xi_chain_interior_canonical_arithmeticization_optimal_order_allOnes n)

/-- Maximum log code length over all Boolean prime-register assignments of length `n`. -/
noncomputable def xi_chain_interior_canonical_arithmeticization_optimal_order_maxLog
    (n : ℕ) : ℝ :=
  let values : Finset ℝ :=
    Finset.univ.image (fun bits : Fin n → Bool =>
      xi_chain_interior_canonical_arithmeticization_optimal_order_logCode n bits)
  values.max' (by
    classical
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)

lemma xi_chain_interior_canonical_arithmeticization_optimal_order_primeLogWeight_nonneg
    (i : ℕ) :
    0 ≤ xi_chain_interior_canonical_arithmeticization_optimal_order_primeLogWeight i := by
  have hprime : Nat.Prime (Nat.nth Nat.Prime i) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
  exact Real.log_nonneg (by exact_mod_cast hprime.one_le)

lemma xi_chain_interior_canonical_arithmeticization_optimal_order_logCode_le_sumLogFirstPrimes
    (n : ℕ) (bits : Fin n → Bool) :
    xi_chain_interior_canonical_arithmeticization_optimal_order_logCode n bits ≤
      xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes n := by
  classical
  unfold xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes
  unfold xi_chain_interior_canonical_arithmeticization_optimal_order_logCode
  refine Finset.sum_le_sum ?_
  intro i _hi
  by_cases hbit : bits i
  · simp [hbit, xi_chain_interior_canonical_arithmeticization_optimal_order_allOnes]
  · simp [hbit, xi_chain_interior_canonical_arithmeticization_optimal_order_allOnes,
      xi_chain_interior_canonical_arithmeticization_optimal_order_primeLogWeight_nonneg i.val]

/-- Paper label: `cor:xi-chain-interior-canonical-arithmeticization-optimal-order`. -/
theorem paper_xi_chain_interior_canonical_arithmeticization_optimal_order (n : ℕ) (hn : 1 ≤ n) :
    xi_chain_interior_canonical_arithmeticization_optimal_order_maxLog n =
      xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes n := by
  classical
  have _hn_used : 1 ≤ n := hn
  unfold xi_chain_interior_canonical_arithmeticization_optimal_order_maxLog
  let allOnes := xi_chain_interior_canonical_arithmeticization_optimal_order_allOnes n
  let values : Finset ℝ :=
    Finset.univ.image (fun bits : Fin n → Bool =>
      xi_chain_interior_canonical_arithmeticization_optimal_order_logCode n bits)
  have hmem :
      xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes n ∈
        values := by
    refine Finset.mem_image.mpr ?_
    exact ⟨allOnes, Finset.mem_univ allOnes, by
      simp [allOnes, xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes]⟩
  have hupper : ∀ y ∈ values,
      y ≤ xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes n := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨bits, _hbits, rfl⟩
    exact xi_chain_interior_canonical_arithmeticization_optimal_order_logCode_le_sumLogFirstPrimes
      n bits
  have hnonempty : values.Nonempty :=
    ⟨xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes n, hmem⟩
  exact (Finset.max'_eq_iff (s := values) (H := hnonempty)
    (a := xi_chain_interior_canonical_arithmeticization_optimal_order_sumLogFirstPrimes n)).mpr
    ⟨hmem, hupper⟩

end Omega.Zeta
