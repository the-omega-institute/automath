import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- The anomaly accumulated by `s` identical anomalous swap labels. -/
def anomSwapTotal {E : Type*} [AddCommMonoid E] (s : ℕ) (label : E) : E :=
  ∑ _ : Fin s, label

lemma norm_anomSwapTotal_le {E : Type*} [SeminormedAddCommGroup E] (s : ℕ) (label : E) :
    ‖anomSwapTotal s label‖ ≤ s * ‖label‖ := by
  unfold anomSwapTotal
  calc
    ‖∑ _ : Fin s, label‖ ≤ ∑ _ : Fin s, ‖label‖ := norm_sum_le _ _
    _ = s * ‖label‖ := by simp

lemma anomSwapTotal_div_step_le {E : Type*} [SeminormedAddCommGroup E]
    (s : ℕ) (label : E) (hlabel : 0 < ‖label‖) :
    ‖anomSwapTotal s label‖ / ‖label‖ ≤ s := by
  have hmain := norm_anomSwapTotal_le s label
  refine (div_le_iff₀ hlabel).2 ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

lemma moment_amplify_norm {W E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (Anom : W → E) (MOM : ℕ → W → W) (q : ℕ) (w : W)
    (hAmp : Anom (MOM q w) = (q : ℝ) • Anom w) :
    ‖Anom (MOM q w)‖ = q * ‖Anom w‖ := by
  rw [hAmp, norm_smul, Real.norm_natCast]

/-- If an anomaly certificate is a sum of at most `s(π)` identical swap labels, then the triangle
inequality gives the swap-count lower bound. Under `q`-fold moment compilation, real scalar
homogeneity turns the anomaly law into linear growth of the lower bound.
    prop:pom-anom-swap-lowerbound-and-mom-amplify -/
theorem paper_pom_anom_swap_lowerbound_and_mom_amplify
    {W E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (Anom : W → E) (MOM : ℕ → W → W) :
    (∀ s : ℕ, ∀ label : E, ‖anomSwapTotal s label‖ ≤ s * ‖label‖) ∧
      (∀ s : ℕ, ∀ label : E, 0 < ‖label‖ → ‖anomSwapTotal s label‖ / ‖label‖ ≤ s) ∧
      (∀ q : ℕ, ∀ w : W, Anom (MOM q w) = (q : ℝ) • Anom w →
        ‖Anom (MOM q w)‖ = q * ‖Anom w‖) ∧
      (∀ q s : ℕ, ∀ label : E, ∀ w : W,
        0 < ‖label‖ →
          Anom (MOM q w) = anomSwapTotal s label →
            Anom (MOM q w) = (q : ℝ) • Anom w →
              q * ‖Anom w‖ / ‖label‖ ≤ s) := by
  refine ⟨norm_anomSwapTotal_le, anomSwapTotal_div_step_le, moment_amplify_norm Anom MOM, ?_⟩
  intro q s label w hlabel hswap hAmp
  have hstep : ‖Anom (MOM q w)‖ / ‖label‖ ≤ s := by
    simpa [hswap] using anomSwapTotal_div_step_le s label hlabel
  rw [moment_amplify_norm Anom MOM q w hAmp] at hstep
  exact hstep

end Omega.POM
