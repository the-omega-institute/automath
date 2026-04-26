import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Zeta.XiCayleyModulusPoissonFourierFingerprint

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Finite weighted Cayley scan area built from the zero-frequency evaluation of each defect
packet. -/
def xi_cayley_scan_area_law_lowfreq_trace_area
    {κ : ℕ} (mass delta : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * xiCayleyModulus (delta j) 0

/-- The corresponding low-frequency trace obtained from the Poisson/Fourier fingerprint of each
packet. -/
def xi_cayley_scan_area_law_lowfreq_trace_lowfreq
    {κ : ℕ} (mass delta : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * (2 * xiFourierFingerprint (delta j))

/-- Paper label: `cor:xi-cayley-scan-area-law-lowfreq-trace`. Summing the single-packet
Cayley-modulus/Poisson/Fourier identity at zero frequency shows that the finite Cayley scan area
is exactly the corresponding low-frequency trace. -/
theorem paper_xi_cayley_scan_area_law_lowfreq_trace
    {κ : ℕ} (mass delta : Fin κ → ℝ)
    (hδ0 : ∀ j : Fin κ, 0 < delta j) (hδ1 : ∀ j : Fin κ, delta j < 1) :
    xi_cayley_scan_area_law_lowfreq_trace_area mass delta =
      xi_cayley_scan_area_law_lowfreq_trace_lowfreq mass delta := by
  unfold xi_cayley_scan_area_law_lowfreq_trace_area
    xi_cayley_scan_area_law_lowfreq_trace_lowfreq
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hpacket :=
    paper_xi_cayley_modulus_poisson_fourier_fingerprint (delta j) (hδ0 j) (hδ1 j)
  rw [hpacket.2]

end

end Omega.Zeta
