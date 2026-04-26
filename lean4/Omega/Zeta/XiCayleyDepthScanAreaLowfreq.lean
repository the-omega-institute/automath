import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The single-layer low-frequency fingerprint used in the finite scan-area law. -/
noncomputable def xi_cayley_depth_scan_area_lowfreq_layer_fourier
    (δ ξ : Real) : Real :=
  if ξ = 0 then
    2 * Real.pi * δ
  else
    Real.pi * (Real.exp (-(1 - δ) * |ξ|) - Real.exp (-(1 + δ) * |ξ|)) / |ξ|

theorem xi_cayley_depth_scan_area_lowfreq_single_layer
    (δ : Real) (_hδ : 0 < δ ∧ δ < 1) :
    (∀ ξ : Real, ξ ≠ 0 →
      xi_cayley_depth_scan_area_lowfreq_layer_fourier δ ξ =
        Real.pi * (Real.exp (-(1 - δ) * |ξ|) - Real.exp (-(1 + δ) * |ξ|)) / |ξ|) ∧
    xi_cayley_depth_scan_area_lowfreq_layer_fourier δ 0 = 2 * Real.pi * δ := by
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    simp [xi_cayley_depth_scan_area_lowfreq_layer_fourier, hξ]
  · simp [xi_cayley_depth_scan_area_lowfreq_layer_fourier]

/-- The finite defect scan area is the zero-frequency Fourier sum of the layered packets. -/
def xi_cayley_depth_scan_area_lowfreq_area {κ : ℕ}
    (mass delta : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * xi_cayley_depth_scan_area_lowfreq_layer_fourier (delta j) 0

/-- The corresponding low-frequency trace. -/
def xi_cayley_depth_scan_area_lowfreq_lowfreq {κ : ℕ}
    (mass delta : Fin κ → ℝ) : ℝ :=
  2 * Real.pi * ∑ j, mass j * delta j

/-- The finite defect Fourier fingerprint assembled termwise from the layered packets. -/
def xi_cayley_depth_scan_area_lowfreq_fourier {κ : ℕ}
    (mass delta : Fin κ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ j, mass j * xi_cayley_depth_scan_area_lowfreq_layer_fourier (delta j) ξ

/-- Paper-facing low-frequency package for finite Cayley depth scans. -/
def xi_cayley_depth_scan_area_lowfreq_statement : Prop :=
  ∀ {κ : ℕ} (mass delta : Fin κ → ℝ),
    (∀ j : Fin κ, 0 < delta j ∧ delta j < 1) →
      xi_cayley_depth_scan_area_lowfreq_area mass delta =
        xi_cayley_depth_scan_area_lowfreq_lowfreq mass delta ∧
      (∀ ξ : ℝ, ξ ≠ 0 →
        xi_cayley_depth_scan_area_lowfreq_fourier mass delta ξ =
          ∑ j, mass j *
            (Real.pi * (Real.exp (-(1 - delta j) * |ξ|) -
              Real.exp (-(1 + delta j) * |ξ|)) / |ξ|)) ∧
      xi_cayley_depth_scan_area_lowfreq_fourier mass delta 0 =
        xi_cayley_depth_scan_area_lowfreq_lowfreq mass delta

theorem paper_xi_cayley_depth_scan_area_lowfreq :
    xi_cayley_depth_scan_area_lowfreq_statement := by
  intro κ mass delta hδ
  refine ⟨?_, ?_, ?_⟩
  · unfold xi_cayley_depth_scan_area_lowfreq_area xi_cayley_depth_scan_area_lowfreq_lowfreq
    calc
      ∑ j, mass j * xi_cayley_depth_scan_area_lowfreq_layer_fourier (delta j) 0 =
          ∑ j, mass j * (2 * Real.pi * delta j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hpacket := xi_cayley_depth_scan_area_lowfreq_single_layer (delta j) (hδ j)
        rw [hpacket.2]
      _ = 2 * Real.pi * ∑ j, mass j * delta j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
  · intro ξ hξ
    unfold xi_cayley_depth_scan_area_lowfreq_fourier
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hpacket := xi_cayley_depth_scan_area_lowfreq_single_layer (delta j) (hδ j)
    rw [hpacket.1 ξ hξ]
  · unfold xi_cayley_depth_scan_area_lowfreq_fourier xi_cayley_depth_scan_area_lowfreq_lowfreq
    calc
      ∑ j, mass j * xi_cayley_depth_scan_area_lowfreq_layer_fourier (delta j) 0 =
          ∑ j, mass j * (2 * Real.pi * delta j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hpacket := xi_cayley_depth_scan_area_lowfreq_single_layer (delta j) (hδ j)
        rw [hpacket.2]
      _ = 2 * Real.pi * ∑ j, mass j * delta j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring

end

end Omega.Zeta
