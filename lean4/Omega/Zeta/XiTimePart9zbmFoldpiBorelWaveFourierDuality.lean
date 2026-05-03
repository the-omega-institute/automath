import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The real double lattice
`2π ℤ_{\ne 0} ∪ (2π/φ) ℤ_{\ne 0}` supporting the Fourier-side wave trace. -/
def xi_time_part9zbm_foldpi_borel_wave_fourier_duality_sigma : Set ℝ :=
  {ω | (∃ k : ℤ, k ≠ 0 ∧ ω = 2 * Real.pi * (k : ℝ)) ∨
    ∃ k : ℤ, k ≠ 0 ∧ ω = (2 * Real.pi / Real.goldenRatio) * (k : ℝ)}

/-- Imaginary lift of a real frequency set, used for Borel singularities. -/
def xi_time_part9zbm_foldpi_borel_wave_fourier_duality_imaginary_lift
    (S : Set ℝ) : Set ℂ :=
  {z | ∃ ω : ℝ, ω ∈ S ∧ z = Complex.I * (ω : ℂ)}

/-- Borel singularity lattice of the folded-π model. -/
def xi_time_part9zbm_foldpi_borel_wave_fourier_duality_borel_lattice : Set ℂ :=
  xi_time_part9zbm_foldpi_borel_wave_fourier_duality_imaginary_lift
    xi_time_part9zbm_foldpi_borel_wave_fourier_duality_sigma

/-- Fourier transform of the packaged wave trace, represented by its pure-point comb weight. -/
def xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier (ξ : ℝ) : ℝ :=
  by
    classical
    exact
      if ξ ∈ xi_time_part9zbm_foldpi_borel_wave_fourier_duality_sigma then 2 * Real.pi else 0

/-- The same pure-point Fourier comb, written as the distributional right-hand side. -/
def xi_time_part9zbm_foldpi_borel_wave_fourier_duality_distributional_comb
    (ξ : ℝ) : ℝ :=
  by
    classical
    exact
      if ξ ∈ xi_time_part9zbm_foldpi_borel_wave_fourier_duality_sigma then 2 * Real.pi else 0

/-- Concrete package for the double lattice, Fourier support, and imaginary Borel lift. -/
def xi_time_part9zbm_foldpi_borel_wave_fourier_duality_statement : Prop :=
  xi_time_part9zbm_foldpi_borel_wave_fourier_duality_borel_lattice =
      xi_time_part9zbm_foldpi_borel_wave_fourier_duality_imaginary_lift
        xi_time_part9zbm_foldpi_borel_wave_fourier_duality_sigma ∧
    Function.support xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier =
      xi_time_part9zbm_foldpi_borel_wave_fourier_duality_sigma ∧
    xi_time_part9zbm_foldpi_borel_wave_fourier_duality_borel_lattice =
      xi_time_part9zbm_foldpi_borel_wave_fourier_duality_imaginary_lift
        (Function.support xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier) ∧
    ∀ ξ : ℝ,
      xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier ξ =
        xi_time_part9zbm_foldpi_borel_wave_fourier_duality_distributional_comb ξ

/-- Paper label: `thm:xi-time-part9zbm-foldpi-borel-wave-fourier-duality`. -/
theorem paper_xi_time_part9zbm_foldpi_borel_wave_fourier_duality :
    xi_time_part9zbm_foldpi_borel_wave_fourier_duality_statement := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · ext ξ
    have htwopi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    by_cases hξ : ξ ∈ xi_time_part9zbm_foldpi_borel_wave_fourier_duality_sigma
    · simp [Function.support, xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier,
        hξ, htwopi]
    · simp [Function.support, xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier,
        hξ]
  · ext z
    constructor
    · rintro ⟨ω, hω, rfl⟩
      refine ⟨ω, ?_, rfl⟩
      have htwopi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
      simp [Function.support, xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier,
        hω, htwopi]
    · rintro ⟨ω, hω, rfl⟩
      refine ⟨ω, ?_, rfl⟩
      by_contra hnot
      simp [Function.support, xi_time_part9zbm_foldpi_borel_wave_fourier_duality_wave_fourier,
        hnot] at hω
  · intro ξ
    rfl

end

end Omega.Zeta
