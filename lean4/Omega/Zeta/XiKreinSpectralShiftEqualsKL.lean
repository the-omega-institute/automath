import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Finite transcript-level KL divergence. -/
def xi_krein_spectral_shift_equals_kl_kl_divergence {n : ℕ}
    (Pα Pβ : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, Pα i * Real.log (Pα i / Pβ i)

/-- Finite Radon--Nikodym entropy integral for the visible spectral laws. -/
def xi_krein_spectral_shift_equals_kl_rn_entropy_integral {n : ℕ}
    (σα σβ : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, σα i * Real.log (σα i / σβ i)

/-- Finite integral of the Krein spectral-shift density. -/
def xi_krein_spectral_shift_equals_kl_spectral_shift_density_integral {n : ℕ}
    (ξ : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, ξ i

/-- Transcript laws identified with the visible sigma-algebra of the spectral measures. -/
def xi_krein_spectral_shift_equals_kl_visible_sigma_identification {n : ℕ}
    (Pα Pβ σα σβ : Fin (n + 1) → ℝ) : Prop :=
  xi_krein_spectral_shift_equals_kl_kl_divergence Pα Pβ =
    xi_krein_spectral_shift_equals_kl_rn_entropy_integral σα σβ

/-- Krein's formula, packaged as the equality between the Radon--Nikodym entropy integral and the
spectral-shift density integral. -/
def xi_krein_spectral_shift_equals_kl_krein_formula {n : ℕ}
    (σα σβ ξ : Fin (n + 1) → ℝ) : Prop :=
  xi_krein_spectral_shift_equals_kl_rn_entropy_integral σα σβ =
    xi_krein_spectral_shift_equals_kl_spectral_shift_density_integral ξ

/-- Paper label: `prop:xi-krein-spectral-shift-equals-kl`.
Once the transcript laws are identified with the visible sigma-algebra of the spectral measures
and Krein's spectral-shift formula is available, the KL divergence is exactly the spectral-shift
integral by two successive rewrites. -/
theorem paper_xi_krein_spectral_shift_equals_kl
    {n : ℕ} (Pα Pβ σα σβ ξ : Fin (n + 1) → ℝ)
    (hVisible :
      xi_krein_spectral_shift_equals_kl_visible_sigma_identification Pα Pβ σα σβ)
    (hKrein : xi_krein_spectral_shift_equals_kl_krein_formula σα σβ ξ) :
    xi_krein_spectral_shift_equals_kl_kl_divergence Pα Pβ =
      xi_krein_spectral_shift_equals_kl_spectral_shift_density_integral ξ := by
  exact hVisible.trans hKrein

end

end Omega.Zeta
