import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeTruncationKernels
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.CircleDimension

open Omega.Zeta

/-- A discrete-side section of the localization quotient fixes every localized integer. -/
def fixesLocalizedIntegers (S : Finset ℕ) (φ : ℚ →+ SupportedLocalizedIntegerGroup S) : Prop :=
  ∀ x : SupportedLocalizedIntegerGroup S, (φ x.1 : ℚ) = x.1

private lemma not_denominatorSupportedBy_inv_prime_not_mem {S : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) : ¬ denominatorSupportedBy S ((p : ℚ)⁻¹) := by
  intro hsupp
  have hden : (((p : ℚ)⁻¹).den) = p := by
    simpa using Rat.inv_natCast_den_of_pos (a := p) hp.pos
  have hdiv : p ∣ (((p : ℚ)⁻¹).den) := by
    simpa [hden] using (dvd_rfl : p ∣ p)
  exact hpS (hsupp p hp hdiv)

/-- Paper label: `cor:cdim-star-no-continuous-section-finite-truncation`. The universal
finite-prime truncation is surjective, but if some prime is omitted from `S` then no additive
section `ℚ → ℤ[1/S]` can restrict to the identity on `ℤ[1/S]`. -/
theorem paper_cdim_star_no_continuous_section_finite_truncation (S : Finset ℕ)
    (hprime : ∃ p : ℕ, p.Prime ∧ p ∉ S) :
    Function.Surjective (universalPrimeTruncationMap S) ∧
      ¬ ∃ φ : ℚ →+ SupportedLocalizedIntegerGroup S, fixesLocalizedIntegers S φ := by
  refine ⟨universalPrimeTruncationMap_surjective S, ?_⟩
  rcases hprime with ⟨p, hp, hpS⟩
  rintro ⟨φ, hfix⟩
  have hφ1 : φ 1 = localizedOne S := by
    ext
    simpa [fixesLocalizedIntegers, localizedOne] using hfix (localizedOne S)
  have hp0Q : (p : ℚ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hsource : (p : ℕ) • ((p : ℚ)⁻¹) = (1 : ℚ) := by
    rw [nsmul_eq_mul]
    field_simp [hp0Q]
  have hmul_sub : (p : ℕ) • φ ((p : ℚ)⁻¹) = localizedOne S := by
    calc
      (p : ℕ) • φ ((p : ℚ)⁻¹) = φ ((p : ℕ) • ((p : ℚ)⁻¹)) := by
        simpa using (φ.map_nsmul ((p : ℚ)⁻¹) p).symm
      _ = φ 1 := by rw [hsource]
      _ = localizedOne S := hφ1
  have hmul_rat : (p : ℚ) * (φ ((p : ℚ)⁻¹) : ℚ) = 1 := by
    have hmul_rat' := congrArg (fun x : SupportedLocalizedIntegerGroup S => (x : ℚ)) hmul_sub
    simpa [localizedOne, nsmul_eq_mul] using hmul_rat'
  have hq : (φ ((p : ℚ)⁻¹) : ℚ) = (p : ℚ)⁻¹ := by
    apply (mul_right_cancel₀ hp0Q)
    calc
      (φ ((p : ℚ)⁻¹) : ℚ) * (p : ℚ) = 1 := by
        simpa [mul_comm] using hmul_rat
      _ = (p : ℚ)⁻¹ * (p : ℚ) := by
        field_simp [hp0Q]
  have hsupported : denominatorSupportedBy S ((p : ℚ)⁻¹) := by
    simpa [hq] using (φ ((p : ℚ)⁻¹)).2
  exact not_denominatorSupportedBy_inv_prime_not_mem hp hpS hsupported

end Omega.CircleDimension
