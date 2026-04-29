import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppCayleyUpperhalfDisk
import Omega.UnitCirclePhaseArithmetic.AppHorizonWeylHerglotz

namespace Omega.UnitCirclePhaseArithmetic

open scoped ComplexConjugate

noncomputable section

/-- The disk-side horizon Carathéodory readout obtained by composing the Weyl model with the
Cayley inverse and the scalar conversion `m ↦ -i m`. -/
def app_horizon_carath_rh_carath (roots : Finset ℂ) (w : ℂ) : ℂ :=
  (-Complex.I) * app_horizon_weyl_herglotz_weyl roots (appCayleyUpperHalfInv w)

/-- Pole-freeness is the same concrete obstruction as on the upper-half-plane side. -/
def app_horizon_carath_rh_pole_free (roots : Finset ℂ) : Prop :=
  app_horizon_weyl_herglotz_pole_free roots

/-- Carathéodory positivity on the disk-side Cayley chart: the real part of the disk readout is
nonnegative on every point coming from the upper half-plane. -/
def app_horizon_carath_rh_positive (roots : Finset ℂ) : Prop :=
  ∀ z, 0 < z.im → 0 ≤ (app_horizon_carath_rh_carath roots (appCayleyUpperHalfMap z)).re

/-- Disk-side RH criterion packaged as the Cayley transport of the already formalized
upper-half-plane Herglotz condition. -/
def app_horizon_carath_rh_statement (roots : Finset ℂ)
    (_hconj : ∀ z ∈ roots, conj z ∈ roots) : Prop :=
  (∀ z ∈ roots, z.im = 0) ↔
    app_horizon_carath_rh_pole_free roots ∧ app_horizon_carath_rh_positive roots

private lemma app_horizon_carath_rh_re_neg_I_mul (z : ℂ) : ((-Complex.I) * z).re = z.im := by
  simp [Complex.mul_re]

private lemma app_horizon_carath_rh_ne_neg_I {z : ℂ} (hz : 0 < z.im) : z ≠ -Complex.I := by
  intro h
  have : 0 < (-Complex.I).im := by simpa [h] using hz
  norm_num at this

/-- Paper label: `cor:app-horizon-carath-rh`. Transporting the Weyl-side Herglotz criterion through
the Cayley relation `𝒞ζ(w) = -i mζ(𝒞⁻¹(w))` turns upper-half-plane imaginary-part positivity into
disk real-part positivity, giving the Carathéodory reformulation of RH for the finite root model. -/
theorem paper_app_horizon_carath_rh (roots : Finset ℂ)
    (hconj : ∀ z ∈ roots, conj z ∈ roots) :
    app_horizon_carath_rh_statement roots hconj := by
  constructor
  · intro hreal
    rcases (paper_app_horizon_weyl_herglotz roots hconj).mp hreal with ⟨hpole, hherg⟩
    refine ⟨hpole, ?_⟩
    intro z hz
    have hz_ne : z ≠ -Complex.I := app_horizon_carath_rh_ne_neg_I hz
    simpa [app_horizon_carath_rh_carath, app_horizon_carath_rh_re_neg_I_mul,
      appCayleyUpperHalf_left_inv hz_ne] using hherg z hz
  · rintro ⟨hpole, hcarath⟩
    apply (paper_app_horizon_weyl_herglotz roots hconj).mpr
    refine ⟨hpole, ?_⟩
    intro z hz
    have hz_ne : z ≠ -Complex.I := app_horizon_carath_rh_ne_neg_I hz
    simpa [app_horizon_carath_rh_carath, app_horizon_carath_rh_re_neg_I_mul,
      appCayleyUpperHalf_left_inv hz_ne] using hcarath z hz

end

end Omega.UnitCirclePhaseArithmetic
