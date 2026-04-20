import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersCrossHomClassification
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Zeta

/-- The Prüfer summands contributed by the quotient `G_T / G_S` in the finite-prime model are
indexed by the new primes in `T \ S`. -/
noncomputable def xiLocalizationQuotientPrueferSummands (S T : Finset Nat) : List Nat :=
  (T \ S).toList

/-- The number of Prüfer summands in the quotient model. -/
def xiLocalizationQuotientPrueferRank (S T : Finset Nat) : Nat :=
  (T \ S).card

/-- In the simplified solenoid model, multiplication by `q = u * m` contributes one cyclic kernel
factor of size `q` for each new Prüfer summand. -/
def xiSolenoidSurjectionKernel (S T : Finset Nat) (u m : Nat) : List Nat :=
  List.replicate (xiLocalizationQuotientPrueferRank S T) (u * m)

/-- Multiplication by an integer on the self-localized discrete model. -/
private def xiLocalizedSelfMultiplication (S : Finset Nat) (q : ℤ) : LocalizedCrossHom S S :=
  ⟨
    { toFun := fun z => z * q
      map_zero' := by simp
      map_add' := by
        intro x y
        ring },
    by
      intro hMissing
      rcases hMissing with ⟨p, hpS, hpNotS⟩
      exact (hpNotS hpS).elim
  ⟩

/-- Paper label: `thm:xi-cdim-localization-quotient-solenoid-surjections`. -/
theorem paper_xi_cdim_localization_quotient_solenoid_surjections
    (S T : Finset Nat) (hST : S ⊆ T) (u m : Nat) :
    let q : ℤ := (u * m : Nat)
    (xiLocalizationQuotientPrueferSummands S T).Nodup ∧
      (∀ ⦃p : Nat⦄, p ∈ S → p ∈ T) ∧
      (∀ ⦃p : Nat⦄, Nat.Prime p → p ∈ xiLocalizationQuotientPrueferSummands S T →
        localizedIndex S p = p ∧ localizedIndex T p = 1) ∧
      (∃! φ : LocalizedCrossHom S S, localizedCrossHomScalar φ = q) ∧
      xiSolenoidSurjectionKernel S T u m =
        List.replicate (xiLocalizationQuotientPrueferRank S T) (u * m) := by
  dsimp
  refine ⟨(T \ S).nodup_toList, hST, ?_, ?_, rfl⟩
  · intro p hp hpList
    have hpDiff : p ∈ T \ S := by
      simpa [xiLocalizationQuotientPrueferSummands] using hpList
    have hpT : p ∈ T := (Finset.mem_sdiff.mp hpDiff).1
    have hpNotS : p ∉ S := (Finset.mem_sdiff.mp hpDiff).2
    exact ⟨(paper_xi_localized_quotient_index_prime_recovery S hp).2.1 hpNotS,
      (paper_xi_localized_quotient_index_prime_recovery T hp).1.1 hpT⟩
  · refine ⟨xiLocalizedSelfMultiplication S ↑(u * m), ?_, ?_⟩
    · simp [xiLocalizedSelfMultiplication, localizedCrossHomScalar]
    · intro φ hφ
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro z
      have hz := localizedCrossHom_eq_mul φ z
      rw [hφ] at hz
      simpa [xiLocalizedSelfMultiplication] using hz

end Omega.Zeta
