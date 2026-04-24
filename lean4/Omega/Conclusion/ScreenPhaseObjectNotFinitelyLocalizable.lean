import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Omega.Conclusion

/-- After the universal-solenoid decomposition, the Pontryagin dual of the rank-`r` screen phase
object is modeled by `ℚ^r`. -/
abbrev ScreenPhasePontryaginDual (r : ℕ) := Fin r → ℚ

/-- The torsion quotient of `(ℚ^r, ℤ^r)` has support at every prime as soon as `r ≠ 0`. -/
def screenPhaseTorsionSupport (r : ℕ) : Set ℕ :=
  {p | Nat.Prime p ∧ r ≠ 0}

/-- The universal all-prime support carried by `(ℚ / ℤ)^r` for `r > 0`. -/
def allPrimeSupport : Set ℕ :=
  {p | Nat.Prime p}

/-- The torsion support coming from one finite-prime localization ledger `ℤ[T⁻¹] / ℤ`. -/
def localizedTorsionSupport (T : Finset ℕ) : Set ℕ :=
  {p | Nat.Prime p ∧ p ∈ T}

/-- The torsion support of a finite direct sum of finite localizations. -/
def finiteLocalizedTorsionSupport (Ts : Finset (Finset ℕ)) : Set ℕ :=
  {p | Nat.Prime p ∧ ∃ T ∈ Ts, p ∈ T}

/-- A prime-support set is finite when it is represented by an explicit finite ledger. -/
def finitePrimeSupport (S : Set ℕ) : Prop :=
  ∃ T : Finset ℕ, ∀ p : ℕ, p ∈ S ↔ p ∈ T

/-- The finite direct sum of localizations only remembers the primes listed in the finite union of
its local ledgers. -/
def finiteLocalizedPrimeLedger (Ts : Finset (Finset ℕ)) : Finset ℕ :=
  (Ts.biUnion id).filter Nat.Prime

/-- Support mismatch obstructing an isomorphism between the screen phase object and a finite
direct sum of finite-prime localizations. -/
def screenPhaseNotFinitelyLocalizable (r : ℕ) (Ts : Finset (Finset ℕ)) : Prop :=
  ∃ p : ℕ, p ∈ screenPhaseTorsionSupport r ∧ p ∉ finiteLocalizedTorsionSupport Ts

lemma finiteLocalizedTorsionSupport_hasFiniteSupport (Ts : Finset (Finset ℕ)) :
    finitePrimeSupport (finiteLocalizedTorsionSupport Ts) := by
  refine ⟨finiteLocalizedPrimeLedger Ts, ?_⟩
  intro p
  constructor
  · intro hp
    have hp' : (∃ T ∈ Ts, p ∈ T) ∧ Nat.Prime p := ⟨hp.2, hp.1⟩
    simpa [finiteLocalizedPrimeLedger] using hp'
  · intro hp
    have hp' : (∃ T ∈ Ts, p ∈ T) ∧ Nat.Prime p := by
      simpa [finiteLocalizedPrimeLedger] using hp
    have hp' : Nat.Prime p ∧ ∃ T ∈ Ts, p ∈ T := ⟨hp'.2, hp'.1⟩
    simpa [finiteLocalizedPrimeLedger, finiteLocalizedTorsionSupport] using hp'

/-- Once the screen phase object has positive rank, its torsion quotient has all-prime support,
whereas any finite direct sum of localized quotients `ℤ[T⁻¹] / ℤ` has only finite-prime support.
Hence a prime survives in the screen-phase torsion quotient but is absent from every finite
localization ledger, obstructing any topological isomorphism.
    cor:conclusion-screen-phase-object-not-finitely-localizable -/
theorem paper_conclusion_screen_phase_object_not_finitely_localizable
    (r : ℕ) (hr : 1 ≤ r) (Ts : Finset (Finset ℕ)) :
    screenPhaseTorsionSupport r = allPrimeSupport ∧
      finitePrimeSupport (finiteLocalizedTorsionSupport Ts) ∧
      screenPhaseNotFinitelyLocalizable r Ts := by
  have hr0 : r ≠ 0 := by omega
  refine ⟨?_, finiteLocalizedTorsionSupport_hasFiniteSupport Ts, ?_⟩
  · ext p
    simp [screenPhaseTorsionSupport, allPrimeSupport, hr0]
  · rcases Nat.exists_infinite_primes ((finiteLocalizedPrimeLedger Ts).sup id + 1) with
      ⟨p, hpge, hpPrime⟩
    have hp_not_mem_ledger : p ∉ finiteLocalizedPrimeLedger Ts := by
      intro hpMem
      have hp_le : p ≤ (finiteLocalizedPrimeLedger Ts).sup id := by
        simpa using (Finset.le_sup hpMem : id p ≤ (finiteLocalizedPrimeLedger Ts).sup id)
      omega
    refine ⟨p, ?_, ?_⟩
    · simp [screenPhaseTorsionSupport, hpPrime, hr0]
    · intro hp
      exact hp_not_mem_ledger <| by
        have hp' : (∃ T ∈ Ts, p ∈ T) ∧ Nat.Prime p := ⟨hp.2, hp.1⟩
        simpa [finiteLocalizedPrimeLedger] using hp'

end Omega.Conclusion
