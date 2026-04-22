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

private lemma gm_entrypoint_divisibility_criterion_le_of_dvd_fib {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hdiv : m ∣ Nat.fib n) : gmFibonacciEntrypoint m ≤ n := by
  unfold gmFibonacciEntrypoint
  rw [dif_pos hm]
  exact Nat.find_min' (exists_gmFibonacciEntrypoint m hm) ⟨hn, hdiv⟩

private lemma gm_entrypoint_divisibility_criterion_iff (m n : ℕ) (hm : 0 < m) :
    m ∣ Nat.fib n ↔ gmFibonacciEntrypoint m ∣ n := by
  constructor
  · intro hdiv
    have hentry : m ∣ Nat.fib (gmFibonacciEntrypoint m) := gmFibonacciEntrypoint_dvd_fib hm
    have hgcd_div : m ∣ Nat.fib (Nat.gcd (gmFibonacciEntrypoint m) n) := by
      rw [Nat.fib_gcd]
      exact dvd_gcd hentry hdiv
    have hgcd_pos : 0 < Nat.gcd (gmFibonacciEntrypoint m) n := by
      exact Nat.gcd_pos_of_pos_left n (gmFibonacciEntrypoint_pos hm)
    have hmin :
        gmFibonacciEntrypoint m ≤ Nat.gcd (gmFibonacciEntrypoint m) n :=
      gm_entrypoint_divisibility_criterion_le_of_dvd_fib hm hgcd_pos hgcd_div
    have hgcd_le : Nat.gcd (gmFibonacciEntrypoint m) n ≤ gmFibonacciEntrypoint m :=
      Nat.gcd_le_left n (gmFibonacciEntrypoint_pos hm)
    have hgcd_eq : Nat.gcd (gmFibonacciEntrypoint m) n = gmFibonacciEntrypoint m :=
      le_antisymm hgcd_le hmin
    have hgcd_eq' : Nat.gcd n (gmFibonacciEntrypoint m) = gmFibonacciEntrypoint m := by
      simpa [Nat.gcd_comm] using hgcd_eq
    exact Nat.gcd_eq_right_iff_dvd.mp hgcd_eq'
  · intro hentry
    exact dvd_trans (gmFibonacciEntrypoint_dvd_fib hm) (Nat.fib_dvd _ _ hentry)

/-- Paper label: `lem:gm-entrypoint-divisibility-criterion`. -/
theorem paper_gm_entrypoint_divisibility_criterion :
    (∀ m n : ℕ, 0 < m → 0 < n → (m ∣ Nat.fib n ↔ gmFibonacciEntrypoint m ∣ n)) ∧
      (∀ p n : ℕ, Nat.Prime p → 0 < n → (p ∣ Nat.fib n ↔ gmFibonacciEntrypoint p ∣ n)) := by
  refine ⟨?_, ?_⟩
  · intro m n hm hn
    exact gm_entrypoint_divisibility_criterion_iff m n hm
  · intro p n hp hn
    exact gm_entrypoint_divisibility_criterion_iff p n hp.pos

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
