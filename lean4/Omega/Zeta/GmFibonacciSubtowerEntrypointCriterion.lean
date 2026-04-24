import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Zeta.XiVisibleArithmeticFibonacciCofinalQuotients

namespace Omega.Zeta

/-- A Fibonacci subtower is cofinal when every positive modulus divides one of its concrete
Fibonacci stages. -/
def GmFibonacciSubtowerCofinal (n : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ k : ℕ, m ∣ foldCongruenceModulus (n k)

lemma exists_gmFibonacciEntrypoint (m : ℕ) (hm : 0 < m) :
    ∃ r : ℕ, 0 < r ∧ m ∣ Nat.fib r := by
  rcases paper_xi_visible_arithmetic_fibonacci_cofinal_quotients hm with ⟨s, hs, hdiv⟩
  refine ⟨s + 2, by omega, ?_⟩
  simpa [foldCongruenceModulus]

/-- The chosen first Fibonacci index at which the modulus `m` appears. -/
noncomputable def gmFibonacciEntrypoint (m : ℕ) : ℕ :=
  if hm : 0 < m then Nat.find (exists_gmFibonacciEntrypoint m hm) else 0

lemma gmFibonacciEntrypoint_pos {m : ℕ} (hm : 0 < m) :
    0 < gmFibonacciEntrypoint m := by
  unfold gmFibonacciEntrypoint
  simp [hm]

lemma gmFibonacciEntrypoint_dvd_fib {m : ℕ} (hm : 0 < m) :
    m ∣ Nat.fib (gmFibonacciEntrypoint m) := by
  have hspec := Nat.find_spec (exists_gmFibonacciEntrypoint m hm)
  unfold gmFibonacciEntrypoint
  simp [hm]
  exact hspec.2

/-- Concrete criterion package: keep the original divisibility chain, show that entrypoint
coverage forces cofinality of the subtower moduli, and identify any such cofinal subtower with the
same profinite completion proxy used elsewhere in the chapter. -/
def GmFibonacciSubtowerEntrypointCriterionStatement (n : ℕ → ℕ) : Prop :=
  (∀ k : ℕ, n k ∣ n (k + 1)) ∧
    ((∀ m : ℕ, 0 < m → ∃ k : ℕ, gmFibonacciEntrypoint m ∣ n k + 2) →
      GmFibonacciSubtowerCofinal n) ∧
    (GmFibonacciSubtowerCofinal n → Nonempty (FibProfiniteCompletion ≃+* Zhat))

/-- Paper label: `thm:gm-fibonacci-subtower-entrypoint-criterion`. -/
theorem paper_gm_fibonacci_subtower_entrypoint_criterion (n : ℕ → ℕ)
    (hchain : ∀ k : ℕ, n k ∣ n (k + 1)) :
    GmFibonacciSubtowerEntrypointCriterionStatement n := by
  refine ⟨hchain, ?_, ?_⟩
  · intro hcover m hm
    rcases hcover m hm with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hentry : m ∣ Nat.fib (gmFibonacciEntrypoint m) :=
      gmFibonacciEntrypoint_dvd_fib hm
    have hfib :
        Nat.fib (gmFibonacciEntrypoint m) ∣ Nat.fib (n k + 2) :=
      Nat.fib_dvd _ _ hk
    exact by
      simpa [foldCongruenceModulus] using dvd_trans hentry hfib
  · intro _
    exact ⟨paper_gm_fibonacci_profinite_axis⟩

end Omega.Zeta
