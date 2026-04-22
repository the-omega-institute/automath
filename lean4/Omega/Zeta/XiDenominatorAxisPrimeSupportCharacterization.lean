import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.Zeta

/-- The element `1 / p` belongs to the localized group `ℤ[S⁻¹]`. -/
def xiPrimeReciprocalInLocalizedGroup (S : FinitePrimeLocalization) (p : ℕ) : Prop :=
  denominatorSupportedBy S ((p : ℚ)⁻¹)

/-- Multiplication by `p` is surjective on the concrete localized additive group. -/
def xiMulByPrimeSurjective (S : FinitePrimeLocalization) (p : ℕ) : Prop :=
  ∀ a : SupportedLocalizedIntegerGroup S,
    ∃ b : SupportedLocalizedIntegerGroup S, (p : ℚ) * b.1 = a.1

/-- The quotient `A / pA` vanishes when every localized element differs from a `p`-multiple by
zero. -/
def xiModPrimeQuotientVanishes (S : FinitePrimeLocalization) (p : ℕ) : Prop :=
  ∀ a : SupportedLocalizedIntegerGroup S,
    ∃ b : SupportedLocalizedIntegerGroup S, a.1 - (p : ℚ) * b.1 = 0

private theorem xi_primeReciprocalInLocalizedGroup_iff {S : FinitePrimeLocalization} {p : ℕ}
    (hp : p.Prime) :
    p ∈ S ↔ xiPrimeReciprocalInLocalizedGroup S p := by
  unfold xiPrimeReciprocalInLocalizedGroup
  constructor
  · intro hpS q hq hqdiv
    have hdivp : q ∣ p := by
      simpa [Rat.inv_natCast_den_of_pos hp.pos] using hqdiv
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdivp
    exact hqp.symm ▸ hpS
  · intro hrec
    have hdiv : p ∣ ((p : ℚ)⁻¹).den := by
      simp [Rat.inv_natCast_den_of_pos hp.pos]
    exact hrec p hp hdiv

private theorem xi_mulByPrimeSurjective_of_mem {S : FinitePrimeLocalization} {p : ℕ}
    (hp : p.Prime) (hpS : p ∈ S) :
    xiMulByPrimeSurjective S p := by
  have hrec : xiPrimeReciprocalInLocalizedGroup S p :=
    (xi_primeReciprocalInLocalizedGroup_iff hp).1 hpS
  intro a
  refine ⟨⟨(p : ℚ)⁻¹ * a.1, denominatorSupportedBy_mul hrec a.2⟩, ?_⟩
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  change (p : ℚ) * ((p : ℚ)⁻¹ * a.1) = a.1
  field_simp [hpq]

private theorem xi_mem_of_mulByPrimeSurjective {S : FinitePrimeLocalization} {p : ℕ}
    (hp : p.Prime) (hsurj : xiMulByPrimeSurjective S p) :
    p ∈ S := by
  obtain ⟨b, hb⟩ := hsurj (localizedOne S)
  have hpq : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hbOne : (p : ℚ) * b.1 = 1 := by
    simpa [localizedOne] using hb
  have hbInv : b.1 = (p : ℚ)⁻¹ := by
    calc
      b.1 = (p : ℚ)⁻¹ * ((p : ℚ) * b.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpq, one_mul]
      _ = (p : ℚ)⁻¹ * 1 := by rw [hbOne]
      _ = (p : ℚ)⁻¹ := by simp
  have hrec : xiPrimeReciprocalInLocalizedGroup S p := by
    unfold xiPrimeReciprocalInLocalizedGroup
    simpa [hbInv] using b.2
  exact (xi_primeReciprocalInLocalizedGroup_iff hp).2 hrec

private theorem xi_mulByPrimeSurjective_iff_modPrimeQuotientVanishes
    (S : FinitePrimeLocalization) (p : ℕ) :
    xiMulByPrimeSurjective S p ↔ xiModPrimeQuotientVanishes S p := by
  constructor
  · intro hsurj a
    obtain ⟨b, hb⟩ := hsurj a
    refine ⟨b, ?_⟩
    linarith
  · intro hvanish a
    obtain ⟨b, hb⟩ := hvanish a
    refine ⟨b, ?_⟩
    linarith

/-- In the concrete localization model `A = ℤ[S⁻¹] ⊆ ℚ`, a prime lies in the support exactly when
`1 / p` is present, equivalently multiplication by `p` is surjective, equivalently the quotient
`A / pA` vanishes.
    prop:xi-denominator-axis-prime-support-characterization -/
theorem paper_xi_denominator_axis_prime_support_characterization_proof
    (S : FinitePrimeLocalization) {p : ℕ} (hp : p.Prime) :
    (p ∈ S ↔ xiPrimeReciprocalInLocalizedGroup S p) ∧
      (p ∈ S ↔ xiMulByPrimeSurjective S p) ∧
      (p ∈ S ↔ xiModPrimeQuotientVanishes S p) := by
  have hrec : p ∈ S ↔ xiPrimeReciprocalInLocalizedGroup S p :=
    xi_primeReciprocalInLocalizedGroup_iff hp
  have hsurj : p ∈ S ↔ xiMulByPrimeSurjective S p := by
    constructor
    · exact xi_mulByPrimeSurjective_of_mem hp
    · exact xi_mem_of_mulByPrimeSurjective hp
  refine ⟨hrec, hsurj, ?_⟩
  exact hsurj.trans (xi_mulByPrimeSurjective_iff_modPrimeQuotientVanishes S p)

def paper_xi_denominator_axis_prime_support_characterization : Prop :=
  ∀ (S : FinitePrimeLocalization) {p : ℕ},
    p.Prime →
      (p ∈ S ↔ xiPrimeReciprocalInLocalizedGroup S p) ∧
        (p ∈ S ↔ xiMulByPrimeSurjective S p) ∧
        (p ∈ S ↔ xiModPrimeQuotientVanishes S p)

end Omega.Zeta
