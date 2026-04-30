import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic
import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Zeta

/-- A one-prime ZG tail word: the singleton prime support is prime-labelled and has no adjacent
distinct prime axes. -/
def xi_time_part9w_zg_positive_density_cofinal_tail_language (p : ℕ) : Prop :=
  Nat.Prime p ∧
    (∀ q ∈ ({p} : Finset ℕ), Nat.Prime q) ∧
      ∀ q ∈ ({p} : Finset ℕ), ∀ r ∈ ({p} : Finset ℕ),
        q ≠ r → q + 2 ≠ r ∧ r + 2 ≠ q

/-- Paper label: `thm:xi-time-part9w-zg-positive-density-cofinal-tail`. -/
theorem paper_xi_time_part9w_zg_positive_density_cofinal_tail
    (W : Omega.Zeta.XiZGAbelResidueLogDensityWitness) :
    W.absoluteConvergenceCriticalLine ∧
      ∀ S : Finset ℕ, ∃ p : ℕ, Nat.Prime p ∧ p ∉ S ∧
        xi_time_part9w_zg_positive_density_cofinal_tail_language p := by
  refine ⟨(paper_xi_zg_abel_residue_log_density W).2.2, ?_⟩
  intro S
  rcases Nat.exists_infinite_primes (S.sup id + 1) with ⟨p, hpge, hpprime⟩
  have hp_not_mem : p ∉ S := by
    intro hpS
    have hp_le : p ≤ S.sup id := by
      simpa using (Finset.le_sup hpS : id p ≤ S.sup id)
    omega
  refine ⟨p, hpprime, hp_not_mem, ?_⟩
  refine ⟨hpprime, ?_, ?_⟩
  · intro q hq
    have hqp : q = p := by
      simpa using hq
    simpa [hqp] using hpprime
  · intro q hq r hr hqr
    simp [Finset.mem_singleton] at hq hr
    subst q
    subst r
    exact (hqr rfl).elim

end Omega.Zeta
