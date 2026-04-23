import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanRationalHerglotzPoleTomography

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-basepoint-scan-kernel-uniqueness`. The rational Herglotz tomography
package already identifies the boundary scan profile, fixes the partial-fraction residues, and
proves uniqueness of the resulting Cauchy kernel expansion. -/
theorem paper_xi_basepoint_scan_kernel_uniqueness
    (D : XiBasepointScanPoleDatum) :
    (∀ x : ℝ, (D.herglotz x).im = D.scanProfile x) ∧
      (∀ G : ℂ → ℂ,
        (∀ z, G z = ∑ k, D.residue k / (z - D.pole k)) →
          G = fun z => ∑ k, D.residue k / (z - D.pole k)) ∧
      (∀ k z, D.herglotzTerm k z = D.residue k / (z - D.pole k)) := by
  exact ⟨(XiBasepointScanPoleDatum.paper_xi_basepoint_scan_rational_herglotz_pole_tomography D).2.1,
    (XiBasepointScanPoleDatum.paper_xi_basepoint_scan_rational_herglotz_pole_tomography D).2.2.1,
    (XiBasepointScanPoleDatum.paper_xi_basepoint_scan_rational_herglotz_pole_tomography D).2.2.2⟩

end Omega.Zeta
