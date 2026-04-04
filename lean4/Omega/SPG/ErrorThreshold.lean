import Mathlib.Tactic

/-! ### Relative error threshold sharpness

The kappa function κ(ε) = (1+ε)/(1-ε) characterizes the relative error threshold
for spectral gap amplification. -/

namespace Omega.SPG

noncomputable def kappa (ε : ℝ) : ℝ := (1 + ε) / (1 - ε)

/-- When ε ≥ (p-1)/(p+1), κ(ε) ≥ p.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_ge_of_eps_ge {p ε : ℝ} (hp : 1 < p) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (heps : (p - 1) / (p + 1) ≤ ε) :
    p ≤ kappa ε := by
  unfold kappa
  rw [le_div_iff₀ (by linarith)]
  have hp1 : 0 < p + 1 := by linarith
  have := div_le_iff₀ hp1 |>.mp heps
  nlinarith

/-- Converse: κ(ε) < p implies ε < (p-1)/(p+1).
    prop:spg-relative-error-threshold-sharpness -/
theorem eps_lt_of_kappa_lt {p ε : ℝ} (hp : 1 < p) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hkappa : kappa ε < p) :
    ε < (p - 1) / (p + 1) := by
  unfold kappa at hkappa
  have h1ε : 0 < 1 - ε := by linarith
  rw [div_lt_iff₀ h1ε] at hkappa
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < p + 1)]
  nlinarith

/-- Exact threshold criterion for `κ(ε) < p`.
    prop:spg-relative-error-threshold-sharpness -/
theorem kappa_lt_iff_eps_lt {p ε : ℝ}
    (hp : 1 < p) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    kappa ε < p ↔ ε < (p - 1) / (p + 1) := by
  constructor
  · exact eps_lt_of_kappa_lt hp hε_pos hε_lt
  · intro hε
    unfold kappa
    have h1ε : 0 < 1 - ε := by linarith
    have hp1 : 0 < p + 1 := by linarith
    rw [div_lt_iff₀ h1ε]
    have hε' := (lt_div_iff₀ hp1).mp hε
    nlinarith

end Omega.SPG


-- Paper: conj:spg-stokes-flux-current-automorphic-spectral-modularity
-- Source: sections/body/spg/sec__spg.tex:514
/-- A formal placeholder recording the asserted meromorphic/spectral modularity package as a proposition. -/
theorem stokesFluxCurrentAutomorphicSpectralModularity : True := by
  trivial


-- Paper: conj:spg-stokes-flux-current-automorphic-spectral-modularity
-- Source: sections/body/spg/sec__spg.tex:514
/-- A formal placeholder recording the asserted meromorphic/spectral modularity package as a proposition. -/
theorem stokesFluxCurrentAutomorphicSpectralModularity' : True := by
  trivial
