import Mathlib.Tactic

namespace Omega.POM

/-- A bounded integer multiple of a positive modulus is zero once its absolute value is
strictly smaller than the modulus. -/
theorem pom_hankel_syndrome_crt_offline_audit_eq_zero_of_dvd_abs_lt
    (x : Int) (M : Nat)
    (hMpos : 0 < (M : Int))
    (hDvd : (M : Int) ∣ x)
    (hAbsLt : |x| < (M : Int)) :
    x = 0 := by
  rcases hDvd with ⟨q, rfl⟩
  by_contra hne
  have hq : q ≠ 0 := by
    intro hq
    apply hne
    simp [hq]
  have hqabs : 1 ≤ |q| := Int.one_le_abs hq
  have hMnonneg : 0 ≤ (M : Int) := le_of_lt hMpos
  have hAbsM : |(M : Int)| = (M : Int) := abs_of_nonneg hMnonneg
  have hge : (M : Int) ≤ |(M : Int) * q| := by
    rw [abs_mul, hAbsM]
    nlinarith
  exact (lt_irrefl (M : Int)) (lt_of_le_of_lt hge hAbsLt)

/-- Paper label: `prop:pom-hankel-syndrome-crt-offline-audit`. Integer residuals whose CRT
product modulus divides them and whose absolute values are bounded by less than half the product
must vanish. -/
theorem paper_pom_hankel_syndrome_crt_offline_audit
    {J K : Type*} (e : J → K → Int) (U M : Nat)
    (hBound : ∀ j k, |e j k| ≤ (U : Int))
    (hProduct : (2 * U : Int) < (M : Int))
    (hCongruences : ∀ j k, (M : Int) ∣ e j k) :
    ∀ j k, e j k = 0 := by
  have hMpos : 0 < (M : Int) := by
    have hTwoUnonneg : (0 : Int) ≤ (2 * U : Int) := by positivity
    linarith
  have hU_lt_M : (U : Int) < (M : Int) := by
    have hUnonneg : (0 : Int) ≤ (U : Int) := by positivity
    nlinarith
  intro j k
  exact pom_hankel_syndrome_crt_offline_audit_eq_zero_of_dvd_abs_lt
    (e j k) M hMpos (hCongruences j k) (lt_of_le_of_lt (hBound j k) hU_lt_M)

end Omega.POM
