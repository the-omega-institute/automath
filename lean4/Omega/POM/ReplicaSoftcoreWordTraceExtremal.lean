import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.POM.ReplicaSoftcoreWordTraceFibonacciFactorization

namespace Omega.POM

/-- The Fibonacci block weight `F_{a+3}` attached to one merged `K`-block. -/
def pom_replica_softcore_word_trace_extremal_block_weight (a : ℕ) : ℕ :=
  Nat.fib (a + 3)

/-- The claimed extremal trace after `r` `J₂`-separations and `k` copies of `K`. -/
def pom_replica_softcore_word_trace_extremal_value (r k : ℕ) : ℕ :=
  2 ^ (r - 1) * Nat.fib (k + 3)

/-- A concrete two-block trace model after the cyclic end blocks have been merged. -/
def pom_replica_softcore_word_trace_extremal_two_block_trace (a b : ℕ) : ℕ :=
  pom_replica_softcore_word_trace_extremal_block_weight a *
    pom_replica_softcore_word_trace_extremal_block_weight b

lemma pom_replica_softcore_word_trace_extremal_fib_merge_identity (a b : ℕ) :
    pom_replica_softcore_word_trace_extremal_two_block_trace a b + Nat.fib a * Nat.fib b =
      2 * Nat.fib (a + b + 3) := by
  simp only [pom_replica_softcore_word_trace_extremal_two_block_trace,
    pom_replica_softcore_word_trace_extremal_block_weight]
  have hadd := Nat.fib_add (a + 2) b
  have ha3 : Nat.fib (a + 3) = Nat.fib (a + 1) + Nat.fib (a + 2) := by
    simpa [Nat.add_assoc, add_comm, add_left_comm] using (Nat.fib_add_two (n := a + 1))
  have ha2 : Nat.fib (a + 2) = Nat.fib a + Nat.fib (a + 1) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := a))
  have hb3 : Nat.fib (b + 3) = Nat.fib (b + 1) + Nat.fib (b + 2) := by
    simpa [Nat.add_assoc, add_comm, add_left_comm] using (Nat.fib_add_two (n := b + 1))
  have hb2 : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := b))
  have hab : Nat.fib (a + b + 3) =
      Nat.fib (a + 2) * Nat.fib b + Nat.fib (a + 3) * Nat.fib (b + 1) := by
    simpa [Nat.add_assoc, add_comm, add_left_comm] using hadd
  rw [ha3, ha2, hb3, hb2, hab]
  rw [ha3, ha2]
  ring_nf

lemma pom_replica_softcore_word_trace_extremal_merge_inequality (a b : ℕ) :
    pom_replica_softcore_word_trace_extremal_two_block_trace a b ≤
      2 * Nat.fib (a + b + 3) := by
  have h := pom_replica_softcore_word_trace_extremal_fib_merge_identity a b
  nlinarith

lemma pom_replica_softcore_word_trace_extremal_single_block_value (k : ℕ) :
    pom_replica_softcore_word_trace_extremal_value 1 k = Nat.fib (k + 3) := by
  simp [pom_replica_softcore_word_trace_extremal_value]

/-- Paper label: `prop:pom-replica-softcore-word-trace-extremal`. This statement records the
Fibonacci factorization interface, the two-block merge inequality that drives the extremal
argument, and the exact value realized when all `K` letters form one block. -/
def pom_replica_softcore_word_trace_extremal_statement : Prop :=
  pom_replica_softcore_word_trace_fibonacci_factorization_statement ∧
    (∀ a b : ℕ,
      pom_replica_softcore_word_trace_extremal_two_block_trace a b ≤
        2 * Nat.fib (a + b + 3)) ∧
    (∀ k : ℕ, pom_replica_softcore_word_trace_extremal_value 1 k = Nat.fib (k + 3))

/-- Paper label: `prop:pom-replica-softcore-word-trace-extremal`. -/
theorem paper_pom_replica_softcore_word_trace_extremal :
    pom_replica_softcore_word_trace_extremal_statement := by
  refine ⟨paper_pom_replica_softcore_word_trace_fibonacci_factorization, ?_, ?_⟩
  · exact pom_replica_softcore_word_trace_extremal_merge_inequality
  · exact pom_replica_softcore_word_trace_extremal_single_block_value

end Omega.POM
