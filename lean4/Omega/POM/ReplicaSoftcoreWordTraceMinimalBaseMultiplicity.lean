import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.POM.ReplicaSoftcoreWordTraceExtremal

namespace Omega.POM

open scoped BigOperators

lemma pom_replica_softcore_word_trace_minimal_base_multiplicity_fib_two_block_lower
    (a b : ℕ) :
    Nat.fib (a + b + 2) ≤ Nat.fib (a + 2) * Nat.fib (b + 2) := by
  have hadd :
      Nat.fib (a + b + 2) =
        Nat.fib (a + 1) * Nat.fib b + Nat.fib (a + 2) * Nat.fib (b + 1) := by
    simpa [Nat.add_assoc, add_comm, add_left_comm] using Nat.fib_add (a + 1) b
  have hmono : Nat.fib (a + 1) ≤ Nat.fib (a + 2) := Nat.fib_mono (by omega)
  have hmul : Nat.fib (a + 1) * Nat.fib b ≤ Nat.fib (a + 2) * Nat.fib b :=
    Nat.mul_le_mul_right (Nat.fib b) hmono
  have hb : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := b))
  calc
    Nat.fib (a + b + 2)
        = Nat.fib (a + 1) * Nat.fib b + Nat.fib (a + 2) * Nat.fib (b + 1) := hadd
    _ ≤ Nat.fib (a + 2) * Nat.fib b + Nat.fib (a + 2) * Nat.fib (b + 1) :=
        Nat.add_le_add_right hmul _
    _ = Nat.fib (a + 2) * (Nat.fib b + Nat.fib (b + 1)) := by ring
    _ = Nat.fib (a + 2) * Nat.fib (b + 2) := by rw [hb]

lemma pom_replica_softcore_word_trace_minimal_base_multiplicity_fib_product_lower
    (r : ℕ) (g : Fin r → ℕ) :
    Nat.fib ((∑ j, (g j + 1)) + 2) ≤ ∏ j, Nat.fib (g j + 3) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
      let s : ℕ := ∑ j : Fin r, (g (Fin.castSucc j) + 1)
      let b : ℕ := g (Fin.last r) + 1
      have hs :
          Nat.fib (s + 2) ≤ ∏ j : Fin r, Nat.fib (g (Fin.castSucc j) + 3) :=
        ih (fun j => g (Fin.castSucc j))
      have hmerge : Nat.fib (s + b + 2) ≤ Nat.fib (s + 2) * Nat.fib (b + 2) :=
        pom_replica_softcore_word_trace_minimal_base_multiplicity_fib_two_block_lower s b
      have hb : Nat.fib (b + 2) = Nat.fib (g (Fin.last r) + 3) := by
        simp [b, Nat.add_assoc]
      calc
        Nat.fib ((s + b) + 2)
            = Nat.fib (s + b + 2) := by omega
        _ ≤ Nat.fib (s + 2) * Nat.fib (b + 2) := hmerge
        _ ≤ (∏ j : Fin r, Nat.fib (g (Fin.castSucc j) + 3)) *
              Nat.fib (g (Fin.last r) + 3) := by
            rw [hb]
            exact Nat.mul_le_mul_right _ hs

/-- Paper label: `cor:pom-replica-softcore-word-trace-minimal-base-multiplicity`. -/
theorem paper_pom_replica_softcore_word_trace_minimal_base_multiplicity
    (m : ℕ) (hm : 1 ≤ m) :
    (∀ r : ℕ, 1 ≤ r → r ≤ m → ∀ g : Fin r → ℕ, (∑ j, g j) = m - r →
      Nat.fib (m + 2) ≤ ∏ j, Nat.fib (g j + 3)) ∧
      (∀ _a : Fin m,
        pom_replica_softcore_word_trace_extremal_value 1 (m - 1) = Nat.fib (m + 2)) ∧
      Fintype.card (Fin m) = m := by
  refine ⟨?_, ?_, ?_⟩
  · intro r _hr hrm g hsum
    have htotal : (∑ j : Fin r, (g j + 1)) = m := by
      rw [Finset.sum_add_distrib, hsum]
      simp [Fintype.card_fin]
      omega
    simpa [htotal] using
      pom_replica_softcore_word_trace_minimal_base_multiplicity_fib_product_lower r g
  · intro _a
    calc
      pom_replica_softcore_word_trace_extremal_value 1 (m - 1) = Nat.fib ((m - 1) + 3) :=
        pom_replica_softcore_word_trace_extremal_single_block_value (m - 1)
      _ = Nat.fib (m + 2) := by
        have hidx :
            m - 1 + 3 = m + 2 := by
          calc
          m - 1 + 3 = (m - 1 + 1) + 2 := by omega
          _ = m + 2 := by rw [Nat.sub_add_cancel hm]
        simp [hidx]
  · simp

end Omega.POM
