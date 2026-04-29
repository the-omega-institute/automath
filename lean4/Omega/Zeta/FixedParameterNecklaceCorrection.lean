import Omega.Zeta.NecklaceCorrection

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part73c-fixed-parameter-necklace-correction`. -/
theorem paper_xi_time_part73c_fixed_parameter_necklace_correction (v : Nat) :
    (∀ m : Nat, Omega.Zeta.necklaceCorrectionKernel v (2 * m + 1) = 0) ∧
      (∀ m : Nat,
        Omega.Zeta.necklaceCorrectionKernel v (2 * m) =
          Finset.sum (Nat.divisors m)
            (fun d => ArithmeticFunction.moebius d * (v : Int) ^ (m / d))) := by
  exact ⟨necklaceCorrectionKernel_odd_eq_zero v, necklaceCorrectionKernel_even v⟩

end Omega.Zeta
