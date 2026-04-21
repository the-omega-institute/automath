import Mathlib
import Omega.Zeta.XiHankelNormalformCRTAdelicMultiplicity

namespace Omega.Zeta

/-- Concrete offline audit data for the Hankel normal-form recovery problem. The matrix
`residual` is the cleared integer discrepancy `F = N* (H₀ Â - H₁)`, the finite prime audit
certificate says that the product of the audited primes divides every entry, and the product is
assumed larger than twice the entrywise sup-norm. -/
structure XiHankelOfflineModularAuditData where
  d : ℕ
  crtData : XiHankelNormalformCRTData
  candidateMatrix : Matrix (Fin d) (Fin d) ℚ
  clearingFactor : ℕ
  residual : Matrix (Fin d) (Fin d) ℤ
  auditPrimes : Finset ℕ
  primesArePrime : ∀ p ∈ auditPrimes, Nat.Prime p
  coprimeModulusDeterminant : Nat.Coprime crtData.modulus crtData.determinant
  primeProduct_gt_doubleSupNorm :
    2 * ((Finset.univ.product Finset.univ).sup fun ij => Int.natAbs (residual ij.1 ij.2)) <
      Finset.prod auditPrimes id
  primeProduct_dvd_entry :
    ∀ i j, ((Finset.prod auditPrimes id : ℕ) : ℤ) ∣ residual i j

namespace XiHankelOfflineModularAuditData

/-- The product of the audited finite primes. -/
def auditPrimeProduct (D : XiHankelOfflineModularAuditData) : ℕ :=
  Finset.prod D.auditPrimes id

/-- The entrywise sup-norm of the cleared residual matrix. -/
def residualSupNorm (D : XiHankelOfflineModularAuditData) : ℕ :=
  (Finset.univ.product Finset.univ).sup fun ij => Int.natAbs (D.residual ij.1 ij.2)

/-- The offline certificate proves both vanishing of the cleared discrepancy and uniqueness of the
CRT solution count imported from the adelic multiplicity theorem. -/
def auditThresholdCertifiesUniqueSolution (D : XiHankelOfflineModularAuditData) : Prop :=
  D.residual = 0 ∧ D.crtData.globalSolutionCount = 1

lemma primeProduct_gt_doubleSupNorm' (D : XiHankelOfflineModularAuditData) :
    2 * D.residualSupNorm < D.auditPrimeProduct := by
  simpa [auditPrimeProduct, residualSupNorm] using D.primeProduct_gt_doubleSupNorm

lemma residual_entry_natAbs_le_supNorm (D : XiHankelOfflineModularAuditData) (i j : Fin D.d) :
    Int.natAbs (D.residual i j) ≤ D.residualSupNorm := by
  change
    Int.natAbs (D.residual i j) ≤
      (Finset.univ.product Finset.univ).sup
        (fun ij : Fin D.d × Fin D.d => Int.natAbs (D.residual ij.1 ij.2))
  have hij : (i, j) ∈ Finset.univ.product Finset.univ := by simp
  exact
    Finset.le_sup
      (f := fun ij : Fin D.d × Fin D.d => Int.natAbs (D.residual ij.1 ij.2))
      hij

lemma int_eq_zero_of_natAbs_lt_of_dvd {n : ℕ} {z : ℤ} (hz : Int.natAbs z < n)
    (hdiv : (n : ℤ) ∣ z) : z = 0 := by
  rcases hdiv with ⟨k, rfl⟩
  by_cases hk : k = 0
  · simp [hk]
  · have hkabs : 0 < Int.natAbs k := Int.natAbs_pos.mpr hk
    have hn : n ≤ Int.natAbs ((n : ℤ) * k) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_mul_of_pos_right _ hkabs
    exact False.elim (Nat.not_lt_of_ge hn hz)

lemma residual_entry_eq_zero (D : XiHankelOfflineModularAuditData) (i j : Fin D.d) :
    D.residual i j = 0 := by
  apply int_eq_zero_of_natAbs_lt_of_dvd
  · have hentry : Int.natAbs (D.residual i j) ≤ D.residualSupNorm :=
      D.residual_entry_natAbs_le_supNorm i j
    have hsup : D.residualSupNorm ≤ 2 * D.residualSupNorm := by
      omega
    exact lt_of_le_of_lt hentry (lt_of_le_of_lt hsup D.primeProduct_gt_doubleSupNorm')
  · simpa [auditPrimeProduct] using D.primeProduct_dvd_entry i j

end XiHankelOfflineModularAuditData

open XiHankelOfflineModularAuditData

/-- Paper label: `prop:xi-hankel-offline-modular-audit-threshold`. Entrywise divisibility by the
audited prime product, together with the strict threshold `P > 2 ‖F‖∞`, forces the cleared
residual matrix to vanish; the previously established CRT-adelic multiplicity theorem then gives
the unique global solution count. -/
theorem paper_xi_hankel_offline_modular_audit_threshold (D : XiHankelOfflineModularAuditData) :
    D.auditThresholdCertifiesUniqueSolution := by
  refine ⟨?_, ?_⟩
  · ext i j
    exact D.residual_entry_eq_zero i j
  · exact
      (paper_xi_hankel_normalform_crt_adelic_multiplicity D.crtData).2.2
        D.coprimeModulusDeterminant

end Omega.Zeta
