import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Paper label: `prop:xi-endpoint-heat-probe-richardson-extrapolation`. If `a N` has leading
term `m + c * s N` and the scale satisfies `s (2N) / s N → λ`, the Richardson combination
cancels the leading scale term and leaves an `o(s N)` remainder. -/
theorem paper_xi_endpoint_heat_probe_richardson_extrapolation (a s : ℕ → ℝ) (m c lambda : ℝ)
    (hLambda : lambda ≠ 1) (hs_nonzero : ∀ᶠ N in atTop, s N ≠ 0)
    (hscale : Tendsto (fun N : ℕ => s (2 * N) / s N) atTop (𝓝 lambda))
    (hmain : Tendsto (fun N : ℕ => (a N - m - c * s N) / s N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (((a (2 * N) - lambda * a N) / (1 - lambda)) - m) / s N)
      atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun N => (a N - m - c * s N) / s N
  let r : ℕ → ℝ := fun N => s (2 * N) / s N
  have htwo : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro N hN
    nlinarith
  have hmain_e : Tendsto e atTop (𝓝 0) := by
    simpa [e] using hmain
  have hmain_e_two : Tendsto (fun N : ℕ => e (2 * N)) atTop (𝓝 0) :=
    hmain_e.comp htwo
  have hscale_r : Tendsto r atTop (𝓝 lambda) := by
    simpa [r] using hscale
  have hden : (1 - lambda) ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm hLambda)
  have halg :
      (fun N : ℕ => (((a (2 * N) - lambda * a N) / (1 - lambda)) - m) / s N) =ᶠ[atTop]
        fun N : ℕ => (c * (r N - lambda) + e (2 * N) * r N - lambda * e N) / (1 - lambda) := by
    filter_upwards [hs_nonzero, htwo.eventually hs_nonzero] with N hsN hs2N
    have hs2N' : s (2 * N) ≠ 0 := hs2N
    dsimp [e, r]
    field_simp [hsN, hs2N', hden]
    ring
  have hnum :
      Tendsto (fun N : ℕ => c * (r N - lambda) + e (2 * N) * r N - lambda * e N)
        atTop (𝓝 (c * (lambda - lambda) + 0 * lambda - lambda * 0)) := by
    exact
      ((tendsto_const_nhds.mul (hscale_r.sub tendsto_const_nhds)).add
        (hmain_e_two.mul hscale_r)).sub (tendsto_const_nhds.mul hmain_e)
  have hquot :
      Tendsto (fun N : ℕ => (c * (r N - lambda) + e (2 * N) * r N - lambda * e N) / (1 - lambda))
        atTop (𝓝 0) := by
    have hquot' :
        Tendsto
          (fun N : ℕ => (c * (r N - lambda) + e (2 * N) * r N - lambda * e N) / (1 - lambda))
          atTop (𝓝 ((c * (lambda - lambda) + 0 * lambda - lambda * 0) / (1 - lambda))) :=
      hnum.div_const (1 - lambda)
    simpa using hquot'
  exact hquot.congr' halg.symm

end Omega.Zeta
