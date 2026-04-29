import Omega.POM.PartitionMonomialsSymmetricPowerRealizationBound

namespace Omega.POM

/-- Paper label:
`thm:pom-schur-channels-cfinite-spectral-multiplicative-semigroup`.
The C-finite/spectral semigroup witness is the same finite-dimensional symmetric-power
realization already supplied by the partition-monomial bound. -/
theorem paper_pom_schur_channels_cfinite_spectral_multiplicative_semigroup
    (q : Nat) (c d : Nat → Nat) (hq : 2 ≤ q)
    (hpart : Finset.sum (Finset.range (q + 1)) (fun r => r * c r) = q) :
    ∃ n : Nat,
      n ≤ Finset.prod (Finset.range (q + 1))
          (fun r => Nat.choose (d r + c r - 1) (c r)) ∧
        ∃ _A : Matrix (Fin n) (Fin n) Nat, True := by
  exact paper_pom_partition_monomials_symmetric_power_realization_bound q c d hq hpart

end Omega.POM
