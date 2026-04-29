import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-basepoint-scan-van-vleck-coeff-residue-bilinear-lock`. Substituting the
leading-coefficient identity `b₀ = -κ(κ+1)` into the residue-moment formula for `b₁`, and then
rewriting `A₁` through the real-part centroid `∑ γ_k`, yields both displayed coefficient
identities. -/
theorem paper_xi_basepoint_scan_van_vleck_coeff_residue_bilinear_lock
    (κ : ℕ) (p r : Fin κ → ℂ) (gamma : Fin κ → ℝ) (A1 b0 b1 : ℝ)
    (hb0 : b0 = -((κ : ℝ) * (κ + 1)))
    (hA1 : A1 = -2 * ∑ k, gamma k)
    (hres1 : 2 * ∑ k, Complex.re (p k * r k) = -((κ : ℝ) * (κ + 1)))
    (hres2 : 2 * ∑ k, Complex.re ((p k) ^ 2 * r k) = b1 - b0 * A1) :
    b0 = 2 * ∑ k, Complex.re (p k * r k) ∧
    b1 = 2 * ∑ k, Complex.re ((p k) ^ 2 * r k) - (κ : ℝ) * (κ + 1) * A1 ∧
    b1 = 2 * ∑ k, Complex.re ((p k) ^ 2 * r k) + 2 * (κ : ℝ) * (κ + 1) * ∑ k, gamma k := by
  have hsecond :
      b1 = 2 * ∑ k, Complex.re ((p k) ^ 2 * r k) - (κ : ℝ) * (κ + 1) * A1 := by
    calc
      b1 = (2 * ∑ k, Complex.re ((p k) ^ 2 * r k)) + b0 * A1 := by linarith [hres2]
      _ = (2 * ∑ k, Complex.re ((p k) ^ 2 * r k)) - (κ : ℝ) * (κ + 1) * A1 := by
        rw [hb0]
        ring
  refine ⟨?_, hsecond, ?_⟩
  · calc
      b0 = -((κ : ℝ) * (κ + 1)) := hb0
      _ = 2 * ∑ k, Complex.re (p k * r k) := hres1.symm
  · calc
      b1 = 2 * ∑ k, Complex.re ((p k) ^ 2 * r k) - (κ : ℝ) * (κ + 1) * A1 := hsecond
      _ = 2 * ∑ k, Complex.re ((p k) ^ 2 * r k) + 2 * (κ : ℝ) * (κ + 1) * ∑ k, gamma k := by
        rw [hA1]
        ring

end Omega.Zeta
