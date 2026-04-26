import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Countable
import Mathlib.Tactic
import Omega.Conclusion.FiniteLocalizedShadowExactTorsionSpectrum
import Omega.Conclusion.ScreenphaseSurjectsAllFiniteLocalizedShadows

namespace Omega.Conclusion

open Omega.Zeta

/-- The prime-indexed family of localized shadows used in the countability argument. -/
def conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_family :
    Set FinitePrimeLocalization :=
  Set.range fun p : Nat.Primes => ({p.1} : FinitePrimeLocalization)

/-- Minimal exact `p`-primary torsion spectrum for the localized shadow `L_T`: at a prime `p`,
the `p`-primary exact-order locus disappears precisely when `p ∈ T`, and otherwise retains the
prime-order size `φ(p)`. -/
def conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_exact_order_count
    (T : FinitePrimeLocalization) (p : ℕ) : ℕ :=
  if Nat.Prime p then
    if p ∈ T then 0 else Nat.totient p
  else
    0

/-- Two localized shadows are separated when some prime has different exact-order torsion count. -/
def conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_nonisomorphic
    (T U : FinitePrimeLocalization) : Prop :=
  ∃ p : ℕ,
    conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_exact_order_count T p ≠
      conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_exact_order_count U p

lemma conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_family_injective :
    Function.Injective
      (fun p : Nat.Primes => ({p.1} : FinitePrimeLocalization)) := by
  intro p q hpq
  apply Subtype.ext
  exact Finset.singleton_injective hpq

lemma conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_prime_singletons
    (p q : Nat.Primes) (hpq : p ≠ q) :
    conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_nonisomorphic
      ({p.1} : FinitePrimeLocalization) ({q.1} : FinitePrimeLocalization) := by
  refine ⟨p.1, ?_⟩
  have hp_not_mem : p.1 ∉ ({q.1} : FinitePrimeLocalization) := by
    simp only [Finset.mem_singleton]
    intro hpq'
    exact hpq (Subtype.ext hpq')
  have htot_pos : 0 < Nat.totient p.1 := by
    rw [Nat.totient_prime p.2]
    have hp_one_lt : 1 < p.1 := p.2.one_lt
    omega
  have hleft :
      conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_exact_order_count
          ({p.1} : FinitePrimeLocalization) p.1 = 0 := by
    simp [conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_exact_order_count,
      p.2]
  have hright :
      conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_exact_order_count
          ({q.1} : FinitePrimeLocalization) p.1 = Nat.totient p.1 := by
    simp [conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_exact_order_count,
      p.2, hp_not_mem]
  rw [hleft, hright]
  exact Nat.ne_of_lt htot_pos

/-- Paper label:
`cor:conclusion-screenphase-countably-many-nonisomorphic-1d-connected-shadows`.
Taking the prime-indexed singleton localizations `L_{ {p} }`, the existing surjection theorem
produces a connected circle-dimensional quotient for each shadow. Distinct primes lie in the
symmetric difference of the corresponding localization ledgers, and the exact prime-order torsion
spectrum separates the two shadows at that prime. Hence the screen phase admits a countable
infinite family of pairwise nonisomorphic connected one-dimensional quotients. -/
theorem paper_conclusion_screenphase_countably_many_nonisomorphic_1d_connected_shadows :
    ∃ F : Set FinitePrimeLocalization,
      F.Countable ∧
        F.Infinite ∧
        (∀ T ∈ F,
          conclusion_screenphase_surjects_all_finite_localized_shadows_statement T 1) ∧
        (∀ T ∈ F, localizedIntegersCircleDimension T = 1) ∧
        (∀ ⦃T U : FinitePrimeLocalization⦄,
          T ∈ F →
            U ∈ F →
              T ≠ U →
                conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_nonisomorphic
                  T U) := by
  refine ⟨conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_family, ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa [conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_family] using
      Set.countable_range (fun p : Nat.Primes => ({p.1} : FinitePrimeLocalization))
  · simpa [conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_family] using
      Set.infinite_range_of_injective
        conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_family_injective
  · intro T hT
    rcases hT with ⟨p, rfl⟩
    simpa using
      paper_conclusion_screenphase_surjects_all_finite_localized_shadows
        ({p.1} : FinitePrimeLocalization) 1 (by decide)
  · intro T hT
    rcases hT with ⟨p, rfl⟩
    rfl
  · intro T U hT hU hTU
    rcases hT with ⟨p, rfl⟩
    rcases hU with ⟨q, rfl⟩
    have hpq : p ≠ q := by
      intro hpq
      apply hTU
      simpa [hpq]
    exact
      conclusion_screenphase_countably_many_nonisomorphic_connected_shadows_prime_singletons p q
        hpq

end Omega.Conclusion
