import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppCayleyUpperhalfDisk
import Omega.UnitCirclePhaseArithmetic.AppHorizonSpectralMeasureAtomic

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators

noncomputable section

/-- The appendix-horizon atomic measure is self-dual under inversion; on the real boundary, the
paired moments are fixed by complex conjugation. -/
def app_horizon_ramanujan_selfdual_measure_statement
    (D : app_horizon_spectral_measure_atomic_data) : Prop :=
  (∀ f : ℂ → ℂ,
      app_horizon_spectral_measure_atomic_measure D (fun ω => f ω⁻¹) =
        app_horizon_spectral_measure_atomic_measure D f) ∧
    (∀ n : ℕ,
      app_horizon_spectral_measure_atomic_moment D n =
        app_horizon_spectral_measure_atomic_measure D (fun ω => (ω⁻¹) ^ n)) ∧
    (∀ _hreal : ∀ ρ ∈ D.roots, ρ.im = 0, ∀ n : ℕ,
      star (app_horizon_spectral_measure_atomic_moment_sum D n) =
        app_horizon_spectral_measure_atomic_moment_sum D n)

private lemma app_horizon_ramanujan_selfdual_measure_real_axis_inv
    {ρ : ℂ} (hρ : ρ.im = 0) :
    star (appCayleyUpperHalfMap ρ) = (appCayleyUpperHalfMap ρ)⁻¹ := by
  have hrepr : ρ = ((ρ.re : ℂ) + (0 : ℝ) * Complex.I) := by
    apply Complex.ext <;> simp [hρ]
  have hnorm : Complex.normSq (appCayleyUpperHalfMap ρ) = 1 := by
    rw [hrepr]
    simpa using appCayleyUpperHalf_normSq_eq_one ρ.re
  have hinv : (appCayleyUpperHalfMap ρ)⁻¹ = star (appCayleyUpperHalfMap ρ) := by
    rw [Complex.inv_def, hnorm]
    simp
  exact hinv.symm

/-- Paper label: `cor:app-horizon-ramanujan-selfdual-measure`. -/
theorem paper_app_horizon_ramanujan_selfdual_measure
    (D : Omega.UnitCirclePhaseArithmetic.app_horizon_spectral_measure_atomic_data) :
    app_horizon_ramanujan_selfdual_measure_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    simp [app_horizon_spectral_measure_atomic_measure, add_comm]
  · intro n
    simp [app_horizon_spectral_measure_atomic_moment, app_horizon_spectral_measure_atomic_measure,
      add_comm]
  · intro hreal n
    revert hreal
    unfold app_horizon_spectral_measure_atomic_moment_sum
    refine Finset.induction_on D.roots ?_ ?_
    · intro hreal
      simp
    · intro ρ s hρ hs hreal
      have hpair :
          star (appCayleyUpperHalfMap ρ) = (appCayleyUpperHalfMap ρ)⁻¹ :=
        app_horizon_ramanujan_selfdual_measure_real_axis_inv (hreal ρ (by simp [hρ]))
      have hsreal : ∀ ρ' ∈ s, ρ'.im = 0 := by
        intro ρ' hρ'
        exact hreal ρ' (by simp [hρ'])
      have htail :
          ∑ x ∈ s, ((starRingEnd ℂ) (appCayleyUpperHalfMap x) ^ n +
              (((starRingEnd ℂ) (appCayleyUpperHalfMap x) ^ n)⁻¹)) =
            ∑ x ∈ s, (appCayleyUpperHalfMap x ^ n + (appCayleyUpperHalfMap x ^ n)⁻¹) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxpair :
            star (appCayleyUpperHalfMap x) = (appCayleyUpperHalfMap x)⁻¹ :=
          app_horizon_ramanujan_selfdual_measure_real_axis_inv (hsreal x hx)
        have hxpair' :
            ((starRingEnd ℂ) (appCayleyUpperHalfMap x) ^ n +
                (((starRingEnd ℂ) (appCayleyUpperHalfMap x) ^ n)⁻¹)) =
              (appCayleyUpperHalfMap x)⁻¹ ^ n + (((appCayleyUpperHalfMap x)⁻¹ ^ n)⁻¹) := by
          simpa using congrArg (fun z : ℂ => z ^ n + (z ^ n)⁻¹) hxpair
        calc
          ((starRingEnd ℂ) (appCayleyUpperHalfMap x) ^ n +
              (((starRingEnd ℂ) (appCayleyUpperHalfMap x) ^ n)⁻¹)) =
              (appCayleyUpperHalfMap x)⁻¹ ^ n + (((appCayleyUpperHalfMap x)⁻¹ ^ n)⁻¹) := hxpair'
          _ = (appCayleyUpperHalfMap x)⁻¹ ^ n + appCayleyUpperHalfMap x ^ n := by
                simp [inv_pow]
          _ = appCayleyUpperHalfMap x ^ n + (appCayleyUpperHalfMap x ^ n)⁻¹ := by
                simp [add_comm, inv_pow]
      simp [hρ, hpair, htail, inv_pow, add_comm]

end

end Omega.UnitCirclePhaseArithmetic
