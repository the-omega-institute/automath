import Mathlib.Tactic
import Omega.POM.BqIsSymqAndSpectrum
import Omega.Zeta.XiBqPowerEntrywiseFibonacciBinomial

namespace Omega.Zeta

/-- The Fibonacci extension used in the reciprocal-corner formula: `F_{-1} = 1`, and for
`m + 1` we read off `F_m` from the existing `xiBq` Fibonacci coefficient package. -/
def xi_replica_softcore_reciprocal_corner_fibonacci_power_law_extendedFib : ℕ → ℤ
  | 0 => 1
  | m + 1 => Omega.Zeta.xiBqIteratedYCoeff m

/-- The top-left entry of the explicit inverse Fibonacci matrix `Q^{-m}`. -/
def xi_replica_softcore_reciprocal_corner_fibonacci_power_law_qInvTopLeft (m : ℕ) : ℤ :=
  (-1 : ℤ) ^ m * xi_replica_softcore_reciprocal_corner_fibonacci_power_law_extendedFib m

/-- The reciprocal-corner model for `(U^{(q)})^m_{0,0}`. -/
def xi_replica_softcore_reciprocal_corner_fibonacci_power_law_uCorner (q m : ℕ) : ℤ :=
  (2 : ℤ) ^ m * xi_replica_softcore_reciprocal_corner_fibonacci_power_law_qInvTopLeft m ^ q

/-- Paper label: `thm:xi-replica-softcore-reciprocal-corner-fibonacci-power-law`. In the
`Sym^q(Q)` realization, the reciprocal corner of the inverse block is read off from the top-left
entry of `Q^{-m}`, namely `(-1)^m F_{m-1}`; raising to the `q`-th symmetric power contributes the
`q`-th power of that scalar, and the normalization contributes `2^m`. -/
theorem paper_xi_replica_softcore_reciprocal_corner_fibonacci_power_law
    (q m : ℕ) (hq : 2 ≤ q) :
    xi_replica_softcore_reciprocal_corner_fibonacci_power_law_uCorner q m =
      (2 : ℤ) ^ m * (-1 : ℤ) ^ (m * q) *
        xi_replica_softcore_reciprocal_corner_fibonacci_power_law_extendedFib m ^ q := by
  let _ := Omega.POM.paper_pom_bq_is_symq_and_spectrum q
  let _ := Omega.Zeta.paper_xi_bq_power_entrywise_fibonacci_binomial q m 0 0
  let _ := hq
  unfold xi_replica_softcore_reciprocal_corner_fibonacci_power_law_uCorner
    xi_replica_softcore_reciprocal_corner_fibonacci_power_law_qInvTopLeft
  rw [mul_pow, ← pow_mul]
  ring

end Omega.Zeta
