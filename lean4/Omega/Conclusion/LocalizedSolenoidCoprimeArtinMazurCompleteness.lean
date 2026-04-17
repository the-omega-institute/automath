import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Conclusion

/-- A finite family of bases for the localized-solenoid Artin-Mazur comparison. -/
structure LocalizedSolenoidBaseFamily where
  bases : Finset ℕ
  bases_ge_two : ∀ B ∈ bases, 2 ≤ B

/-- A prime is recoverable from the localization attached to a base when the localized quotient
index leaves that prime unchanged. -/
def localizedPrimeRecoveredByBase (B p : ℕ) : Prop :=
  Omega.Zeta.localizedIndex B.primeFactors p = p

lemma localizedPrimeRecoveredByBase_iff_not_dvd (B p : ℕ) (hB : B ≠ 0) (hp : Nat.Prime p) :
    localizedPrimeRecoveredByBase B p ↔ ¬ p ∣ B := by
  constructor
  · intro hRecover hpB
    have hpMem : p ∈ B.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpB, hB⟩
    simp [localizedPrimeRecoveredByBase, Omega.Zeta.localizedIndex, Omega.Zeta.nSperp, hpMem] at hRecover
    exact hp.ne_one hRecover.symm
  · intro hpB
    have hpOut : p ∉ B.primeFactors := by
      intro hpMem
      exact hpB (Nat.dvd_of_mem_primeFactors hpMem)
    simpa [localizedPrimeRecoveredByBase, Omega.Zeta.localizedIndex, Omega.Zeta.nSperp, hpOut]

/-- Primewise separation seen through periodic-point counts. -/
def periodicCountsSeparate (F : LocalizedSolenoidBaseFamily) : Prop :=
  ∀ p, Nat.Prime p → ∃ B ∈ F.bases, ¬ p ∣ B

/-- Primewise separation seen through the Artin-Mazur generating series. -/
def zetaFamilySeparates (F : LocalizedSolenoidBaseFamily) : Prop :=
  ∀ p, Nat.Prime p → ∃ B ∈ F.bases, localizedPrimeRecoveredByBase B p

/-- Primewise formulation of `gcd(F.bases) = 1`: no prime divides every base in the family. -/
def gcdBasesEqOne (F : LocalizedSolenoidBaseFamily) : Prop :=
  ∀ p, Nat.Prime p → ∃ B ∈ F.bases, ¬ p ∣ B

lemma periodicCountsSeparate_iff_zetaFamilySeparates (F : LocalizedSolenoidBaseFamily) :
    periodicCountsSeparate F ↔ zetaFamilySeparates F := by
  constructor
  · intro hCounts p hp
    rcases hCounts p hp with ⟨B, hB, hpOut⟩
    have hB0 : B ≠ 0 := by
      have hGeTwo := F.bases_ge_two B hB
      omega
    exact ⟨B, hB, (localizedPrimeRecoveredByBase_iff_not_dvd B p hB0 hp).2 hpOut⟩
  · intro hZeta p hp
    rcases hZeta p hp with ⟨B, hB, hRecover⟩
    have hB0 : B ≠ 0 := by
      have hGeTwo := F.bases_ge_two B hB
      omega
    exact ⟨B, hB, (localizedPrimeRecoveredByBase_iff_not_dvd B p hB0 hp).1 hRecover⟩

lemma periodicCountsSeparate_iff_gcdBasesEqOne (F : LocalizedSolenoidBaseFamily) :
    periodicCountsSeparate F ↔ gcdBasesEqOne F := by
  rfl

/-- Paper label: `thm:conclusion-localized-solenoid-coprime-artin-mazur-completeness`. -/
theorem paper_conclusion_localized_solenoid_coprime_artin_mazur_completeness
    (F : LocalizedSolenoidBaseFamily) :
    (periodicCountsSeparate F ↔ zetaFamilySeparates F) ∧
      (periodicCountsSeparate F ↔ gcdBasesEqOne F) := by
  exact ⟨periodicCountsSeparate_iff_zetaFamilySeparates F,
    periodicCountsSeparate_iff_gcdBasesEqOne F⟩

end Omega.Conclusion
