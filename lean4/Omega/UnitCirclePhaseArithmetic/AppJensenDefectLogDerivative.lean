import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppJensenSingleZeroLowerBound

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators

noncomputable section

/-- The zero-counting function in radius coordinates for the finite Jensen model. -/
def appJensenZeroCount (roots : Finset ℂ) (ρ : ℝ) : ℕ :=
  (roots.filter fun z => ‖z‖ < ρ).card

/-- The finite Jensen defect viewed in logarithmic radius coordinates. -/
def appJensenLogRadiusDefect (roots : Finset ℂ) (t : ℝ) : ℝ :=
  Finset.sum roots fun z => max (t - Real.log ‖z‖) (0 : ℝ)

private lemma appJensenLogRadiusDefect_eq_exp (roots : Finset ℂ)
    (hroot_pos : ∀ z ∈ roots, 0 < ‖z‖) (t : ℝ) :
    appJensenLogRadiusDefect roots t = appSingleZeroJensenDefect (Real.exp t) roots := by
  unfold appJensenLogRadiusDefect appSingleZeroJensenDefect
  refine Finset.sum_congr rfl ?_
  intro z hz
  rw [Real.log_div (by positivity) (ne_of_gt (hroot_pos z hz)), Real.log_exp]

private lemma appJensenZeroCount_eq_indicator_sum (roots : Finset ℂ)
    (hroot_pos : ∀ z ∈ roots, 0 < ‖z‖) (t : ℝ) :
    (appJensenZeroCount roots (Real.exp t) : ℝ) =
      Finset.sum roots fun z => if Real.log ‖z‖ < t then (1 : ℝ) else 0 := by
  rw [appJensenZeroCount]
  calc
    (((roots.filter fun z => ‖z‖ < Real.exp t).card : ℕ) : ℝ)
        = Finset.sum (roots.filter fun z => ‖z‖ < Real.exp t) fun _ => (1 : ℝ) := by simp
    _ = Finset.sum roots fun z => if Real.log ‖z‖ < t then (1 : ℝ) else 0 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro z hz
          by_cases hzlt : ‖z‖ < Real.exp t
          · have hloglt : Real.log ‖z‖ < t := by
              have := Real.log_lt_log (hroot_pos z hz) hzlt
              simpa [Real.log_exp] using this
            simp [hzlt, hloglt]
          · have hnotloglt : ¬ Real.log ‖z‖ < t := by
              intro hloglt
              apply hzlt
              have hlogexp : Real.log ‖z‖ < Real.log (Real.exp t) := by
                simpa [Real.log_exp] using hloglt
              exact (Real.log_lt_log_iff (hroot_pos z hz) (by positivity)).mp hlogexp
            simp [hzlt, hnotloglt]

private lemma appJensenLogRadiusTerm_hasDerivAt (z : ℂ) {t : ℝ}
    (hshell : t ≠ Real.log ‖z‖) :
    HasDerivAt (fun s : ℝ => max (s - Real.log ‖z‖) (0 : ℝ))
      (if Real.log ‖z‖ < t then 1 else 0) t := by
  by_cases hlt : Real.log ‖z‖ < t
  · have hderiv : HasDerivAt (fun s : ℝ => s - Real.log ‖z‖) 1 t := by
      simpa using (hasDerivAt_id t).sub_const (Real.log ‖z‖)
    have heq :
        (fun s : ℝ => max (s - Real.log ‖z‖) (0 : ℝ)) =ᶠ[nhds t]
          fun s => s - Real.log ‖z‖ := by
      filter_upwards [Ioi_mem_nhds hlt] with s hs
      have hsle : Real.log ‖z‖ ≤ s := le_of_lt hs
      simp [hsle]
    simpa [hlt] using hderiv.congr_of_eventuallyEq heq
  · have hgt : t < Real.log ‖z‖ := lt_of_le_of_ne (le_of_not_gt hlt) hshell
    have hderiv : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := by
      simpa using hasDerivAt_const t (0 : ℝ)
    have heq :
        (fun s : ℝ => max (s - Real.log ‖z‖) (0 : ℝ)) =ᶠ[nhds t]
          fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hgt] with s hs
      have hsle : s ≤ Real.log ‖z‖ := le_of_lt hs
      simp [hsle]
    simpa [hlt] using hderiv.congr_of_eventuallyEq heq

private lemma appJensenLogRadiusDefect_hasDerivAt (roots : Finset ℂ)
    (hroot_pos : ∀ z ∈ roots, 0 < ‖z‖) {t : ℝ}
    (hshell : ∀ z ∈ roots, ‖z‖ ≠ Real.exp t) :
    HasDerivAt (appJensenLogRadiusDefect roots) (appJensenZeroCount roots (Real.exp t)) t := by
  change HasDerivAt (fun s : ℝ => Finset.sum roots fun z => max (s - Real.log ‖z‖) (0 : ℝ))
    (appJensenZeroCount roots (Real.exp t)) t
  have hsum :=
    (HasDerivAt.sum (u := roots) (x := t)
      (A := fun z => fun s : ℝ => max (s - Real.log ‖z‖) (0 : ℝ))
      (A' := fun z => if Real.log ‖z‖ < t then (1 : ℝ) else 0)
      (fun z hz => appJensenLogRadiusTerm_hasDerivAt z (by
        intro hEq
        have hexp : ‖z‖ = Real.exp t := by
          calc
            ‖z‖ = Real.exp (Real.log ‖z‖) := by rw [Real.exp_log (hroot_pos z hz)]
            _ = Real.exp t := by rw [hEq.symm]
        exact hshell z hz hexp)))
  convert hsum using 1
  · ext s
    simp
  · exact appJensenZeroCount_eq_indicator_sum roots hroot_pos t

private lemma appJensenLogRadiusDefect_continuous (roots : Finset ℂ) :
    Continuous (appJensenLogRadiusDefect roots) := by
  classical
  induction roots using Finset.induction_on with
  | empty =>
      simpa [appJensenLogRadiusDefect] using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  | @insert z roots hz ih =>
      have hterm : Continuous (fun t : ℝ => max (t - Real.log ‖z‖) (0 : ℝ)) :=
        (continuous_id.sub continuous_const).max continuous_const
      have ih' : Continuous (fun t : ℝ => Finset.sum roots fun w => max (t - Real.log ‖w‖) (0 : ℝ)) := by
        simpa [appJensenLogRadiusDefect] using ih
      unfold appJensenLogRadiusDefect
      simpa [Finset.sum_insert, hz] using hterm.add ih'

private lemma appJensenLogRadiusDefect_monotone (roots : Finset ℂ) :
    Monotone (appJensenLogRadiusDefect roots) := by
  intro t₁ t₂ ht
  change
    Finset.sum roots (fun z => max (t₁ - Real.log ‖z‖) (0 : ℝ)) ≤
      Finset.sum roots (fun z => max (t₂ - Real.log ‖z‖) (0 : ℝ))
  refine Finset.sum_le_sum ?_
  intro z hz
  exact max_le_max (sub_le_sub_right ht _) (show (0 : ℝ) ≤ 0 by rfl)

private lemma appJensenLogRadiusDefect_zero_propagates (roots : Finset ℂ)
    {t t₀ : ℝ} (ht : t ≤ t₀) (hzero : appJensenLogRadiusDefect roots t₀ = 0) :
    appJensenLogRadiusDefect roots t = 0 := by
  have hnonneg : 0 ≤ appJensenLogRadiusDefect roots t := by
    unfold appJensenLogRadiusDefect
    refine Finset.sum_nonneg ?_
    intro z hz
    exact le_max_right _ _
  have hmono := appJensenLogRadiusDefect_monotone roots ht
  linarith

/-- Paper label: `prop:app-jensen-defect-log-derivative`.
The finite Jensen defect in logarithmic radius coordinates is a finite sum of hinge functions.
Away from shell radii its derivative is exactly the zero-counting function, and the same explicit
formula yields continuity, monotonicity, and hereditary vanishing. -/
theorem paper_app_jensen_defect_log_derivative
    (roots : Finset ℂ) (hroot_pos : ∀ z ∈ roots, 0 < ‖z‖) :
    (∀ {t : ℝ}, (∀ z ∈ roots, ‖z‖ ≠ Real.exp t) →
      HasDerivAt (fun s => appSingleZeroJensenDefect (Real.exp s) roots)
        (appJensenZeroCount roots (Real.exp t)) t) ∧
      Continuous (fun t => appSingleZeroJensenDefect (Real.exp t) roots) ∧
      Monotone (fun t => appSingleZeroJensenDefect (Real.exp t) roots) ∧
      (∀ {t t₀ : ℝ}, t ≤ t₀ →
        appSingleZeroJensenDefect (Real.exp t₀) roots = 0 →
          appSingleZeroJensenDefect (Real.exp t) roots = 0) := by
  have hdefect_eq :
      (fun t => appSingleZeroJensenDefect (Real.exp t) roots) = appJensenLogRadiusDefect roots := by
    funext t
    symm
    exact appJensenLogRadiusDefect_eq_exp roots hroot_pos t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t hshell
    simpa [hdefect_eq] using appJensenLogRadiusDefect_hasDerivAt roots hroot_pos hshell
  · simpa [hdefect_eq] using appJensenLogRadiusDefect_continuous roots
  · simpa [hdefect_eq] using appJensenLogRadiusDefect_monotone roots
  · intro t t₀ ht hzero
    have hzero' : appJensenLogRadiusDefect roots t₀ = 0 := by
      simpa [appJensenLogRadiusDefect_eq_exp roots hroot_pos t₀] using hzero
    rw [← appJensenLogRadiusDefect_eq_exp roots hroot_pos t]
    exact appJensenLogRadiusDefect_zero_propagates roots ht hzero'

end

end Omega.UnitCirclePhaseArithmetic
