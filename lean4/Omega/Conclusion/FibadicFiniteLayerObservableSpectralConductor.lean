import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Finite Fourier support of a finitely presented observable. -/
def conclusion_fibadic_finite_layer_observable_spectral_conductor_fourierSupport
    {χ : Type*} [Fintype χ] [DecidableEq χ] (coeff : χ → ℤ) : Finset χ :=
  Finset.univ.filter fun character => coeff character ≠ 0

/-- The observable is visible at depth `d` exactly when every active spectral depth divides `d`. -/
def conclusion_fibadic_finite_layer_observable_spectral_conductor_visibleAtDepth
    {χ : Type*} [Fintype χ] [DecidableEq χ]
    (coeff : χ → ℤ) (spectralDepth : χ → ℕ) (d : ℕ) : Prop :=
  ∀ character ∈
    conclusion_fibadic_finite_layer_observable_spectral_conductor_fourierSupport coeff,
      spectralDepth character ∣ d

/-- The finite-layer observable depth is the lcm of the active spectral depths. -/
def conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth
    {χ : Type*} [Fintype χ] [DecidableEq χ]
    (coeff : χ → ℤ) (spectralDepth : χ → ℕ) : ℕ :=
  (conclusion_fibadic_finite_layer_observable_spectral_conductor_fourierSupport coeff).lcm
    spectralDepth

/-- Arithmetic conductor depth obtained by taking the lcm of active character conductors. -/
def conclusion_fibadic_finite_layer_observable_spectral_conductor_conductorDepth
    {χ : Type*} [Fintype χ] [DecidableEq χ]
    (coeff : χ → ℤ) (characterConductorDepth : χ → ℕ) : ℕ :=
  (conclusion_fibadic_finite_layer_observable_spectral_conductor_fourierSupport coeff).lcm
    characterConductorDepth

lemma conclusion_fibadic_finite_layer_observable_spectral_conductor_visible_iff
    {χ : Type*} [Fintype χ] [DecidableEq χ]
    (coeff : χ → ℤ) (spectralDepth : χ → ℕ) (d : ℕ) :
    conclusion_fibadic_finite_layer_observable_spectral_conductor_visibleAtDepth
        coeff spectralDepth d ↔
      conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth
        coeff spectralDepth ∣ d := by
  rw [conclusion_fibadic_finite_layer_observable_spectral_conductor_visibleAtDepth,
    conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth]
  exact (Finset.lcm_dvd_iff).symm

lemma conclusion_fibadic_finite_layer_observable_spectral_conductor_lcm_rewrite
    {χ : Type*} [Fintype χ] [DecidableEq χ]
    (coeff : χ → ℤ) (spectralDepth characterConductorDepth : χ → ℕ)
    (hconductor :
      ∀ character ∈
        conclusion_fibadic_finite_layer_observable_spectral_conductor_fourierSupport coeff,
          characterConductorDepth character = spectralDepth character) :
    conclusion_fibadic_finite_layer_observable_spectral_conductor_conductorDepth
        coeff characterConductorDepth =
      conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth
        coeff spectralDepth := by
  rw [conclusion_fibadic_finite_layer_observable_spectral_conductor_conductorDepth,
    conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth]
  apply dvd_antisymm
  · exact Finset.lcm_dvd fun character hcharacter => by
      rw [hconductor character hcharacter]
      exact Finset.dvd_lcm hcharacter
  · exact Finset.lcm_dvd fun character hcharacter => by
      rw [← hconductor character hcharacter]
      exact Finset.dvd_lcm hcharacter

/-- Paper label: `thm:conclusion-fibadic-finite-layer-observable-spectral-conductor`.
For a finite Fourier support, visibility at depth `d` is equivalent to divisibility by the lcm of
all active spectral depths; if character conductor depth agrees with spectral depth on the
support, the arithmetic conductor lcm is the same number. -/
theorem paper_conclusion_fibadic_finite_layer_observable_spectral_conductor
    {χ : Type*} [Fintype χ] [DecidableEq χ]
    (coeff : χ → ℤ) (spectralDepth characterConductorDepth : χ → ℕ)
    (hconductor :
      ∀ character ∈
        conclusion_fibadic_finite_layer_observable_spectral_conductor_fourierSupport coeff,
          characterConductorDepth character = spectralDepth character) :
    (∀ d : ℕ,
      conclusion_fibadic_finite_layer_observable_spectral_conductor_visibleAtDepth
          coeff spectralDepth d ↔
        conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth
          coeff spectralDepth ∣ d) ∧
      conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth
          coeff spectralDepth =
        (conclusion_fibadic_finite_layer_observable_spectral_conductor_fourierSupport coeff).lcm
          spectralDepth ∧
        conclusion_fibadic_finite_layer_observable_spectral_conductor_conductorDepth
            coeff characterConductorDepth =
          conclusion_fibadic_finite_layer_observable_spectral_conductor_observableDepth
            coeff spectralDepth := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    exact
      conclusion_fibadic_finite_layer_observable_spectral_conductor_visible_iff
        coeff spectralDepth d
  · rfl
  · exact
      conclusion_fibadic_finite_layer_observable_spectral_conductor_lcm_rewrite
        coeff spectralDepth characterConductorDepth hconductor

end Omega.Conclusion
