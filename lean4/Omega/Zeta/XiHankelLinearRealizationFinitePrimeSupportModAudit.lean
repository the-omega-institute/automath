import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-hankel-linear-realization-finite-prime-support-mod-audit`. -/
theorem paper_xi_hankel_linear_realization_finite_prime_support_mod_audit
    (det : Int) (BadPrime GoodPrimeUniqueSolution : Nat -> Prop)
    (hdet : det ≠ 0)
    (hbad : forall p, BadPrime p ↔ Nat.Prime p ∧ (p : Int) ∣ det)
    (hgood : forall p, Nat.Prime p -> ¬ BadPrime p -> GoodPrimeUniqueSolution p) :
    (exists bads : List Nat, forall p, BadPrime p -> p ∈ bads) ∧
      forall p, Nat.Prime p -> ¬ BadPrime p -> GoodPrimeUniqueSolution p := by
  constructor
  · refine ⟨(Nat.divisors det.natAbs).toList, ?_⟩
    intro p hpbad
    have hp_dvd_int : (p : Int) ∣ det := (hbad p).mp hpbad |>.2
    have hp_dvd_natAbs : p ∣ det.natAbs := by
      exact Int.natAbs_dvd_natAbs.mpr hp_dvd_int
    have hdet_natAbs : det.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hdet
    rw [Finset.mem_toList, Nat.mem_divisors]
    exact ⟨hp_dvd_natAbs, hdet_natAbs⟩
  · exact hgood

end Omega.Zeta
