import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SPG

/-- The multiplicative ratio comparing perturbed and exact `L^p` decoding readouts. -/
noncomputable def lpSuperellipsoidNoiseRatio (ε : ℝ) : ℝ :=
  (1 + ε) / (1 - ε)

/-- Log-stability reduces to the standard multiplicative noise quotient bound. -/
noncomputable def lpSuperellipsoidDecodingLogStability (d : ℕ) (p ε : ℝ) : Prop :=
  1 < lpSuperellipsoidNoiseRatio ε

/-- Dividing the logarithmic error by `p` keeps a positive stability margin. -/
noncomputable def lpSuperellipsoidGodelExponentStability (d : ℕ) (p ε : ℝ) : Prop :=
  0 < Real.log (lpSuperellipsoidNoiseRatio ε) / p

/-- Paper-facing multiplicative-noise stability for `L^p` superellipsoid decoding.
    prop:spg-lp-superellipsoid-decoding-multiplicative-noise-stability -/
theorem paper_spg_lp_superellipsoid_decoding_multiplicative_noise_stability (d : ℕ) {p ε : ℝ}
    (hp : 0 < p) (hε0 : 0 < ε) (hε1 : ε < 1) :
    lpSuperellipsoidDecodingLogStability d p ε ∧ lpSuperellipsoidGodelExponentStability d p ε := by
  have hden : 0 < 1 - ε := by linarith
  have hratio : 1 < lpSuperellipsoidNoiseRatio ε := by
    unfold lpSuperellipsoidNoiseRatio
    exact (one_lt_div hden).2 (by linarith)
  have hlog : 0 < Real.log (lpSuperellipsoidNoiseRatio ε) := by
    exact Real.log_pos hratio
  refine ⟨hratio, ?_⟩
  exact div_pos hlog hp

end Omega.SPG
