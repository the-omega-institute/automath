import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Omega.Zeta.RecursiveZeroShadowingExplicit

namespace Omega.Zeta

/-- Concrete one-step recursion data for the zero-drift statement on a shadow window. The next
iterate is `fNext = fCurr + perturb`, the current iterate vanishes at `tau`, the next iterate has
a unique sign change on the window, and its derivative stays uniformly away from `0`. -/
structure XiResolutionRecursionZeroDriftData where
  fCurr : ℝ → ℝ
  fNext : ℝ → ℝ
  perturb : ℝ → ℝ
  tau : ℝ
  r : ℝ
  m : ℝ
  perturbSup : ℝ
  hr : 0 < r
  hm : 0 < m
  recursion : ∀ t, fNext t = fCurr t + perturb t
  tau_zero : fCurr tau = 0
  continuous_next : ContinuousOn fNext (xiShadowWindow tau r)
  strictMono_next : StrictMonoOn fNext (xiShadowWindow tau r)
  differentiable_next : DifferentiableOn ℝ fNext (xiShadowWindow tau r)
  deriv_lower : ∀ t ∈ xiShadowWindow tau r, m ≤ |deriv fNext t|
  left_nonpos : fNext (tau - r) ≤ 0
  right_nonneg : 0 ≤ fNext (tau + r)
  perturbSup_nonneg : 0 ≤ perturbSup
  perturb_bound : ∀ t ∈ xiShadowWindow tau r, |perturb t| ≤ perturbSup
  perturbSup_lt : perturbSup < m * r

namespace XiResolutionRecursionZeroDriftData

/-- The next iterate has a unique zero in the current shadow window. -/
def nextZeroExistsUnique (D : XiResolutionRecursionZeroDriftData) : Prop :=
  ∃! t, t ∈ xiShadowWindow D.tau D.r ∧ D.fNext t = 0

/-- The zero drift is governed by the perturbation evaluated at the previous zero and a mean-value
derivative sampled along the segment joining the old and new zeros. -/
def nextZeroDriftIdentity (D : XiResolutionRecursionZeroDriftData) : Prop :=
  ∃ t, t ∈ xiShadowWindow D.tau D.r ∧ D.fNext t = 0 ∧
    ∃ ξ ∈ Set.uIcc D.tau t, t - D.tau = -D.perturb D.tau / deriv D.fNext ξ

/-- Every zero of the next iterate in the current shadow window obeys the explicit drift bound
coming from the uniform perturbation envelope and the derivative lower bound. -/
def nextZeroDriftBound (D : XiResolutionRecursionZeroDriftData) : Prop :=
  ∀ t, t ∈ xiShadowWindow D.tau D.r → D.fNext t = 0 → |t - D.tau| ≤ D.perturbSup / D.m

end XiResolutionRecursionZeroDriftData

private lemma tau_mem_window (D : XiResolutionRecursionZeroDriftData) :
    D.tau ∈ xiShadowWindow D.tau D.r := by
  show D.tau ∈ Set.Icc (D.tau - D.r) (D.tau + D.r)
  exact ⟨by linarith [D.hr], by linarith [D.hr]⟩

private lemma next_at_tau_eq_perturb (D : XiResolutionRecursionZeroDriftData) :
    D.fNext D.tau = D.perturb D.tau := by
  simpa [D.tau_zero] using D.recursion D.tau

private lemma uIcc_subset_window (D : XiResolutionRecursionZeroDriftData) {t : ℝ}
    (ht : t ∈ xiShadowWindow D.tau D.r) :
    Set.uIcc D.tau t ⊆ xiShadowWindow D.tau D.r := by
  intro x hx
  have hx' : x ∈ Set.Icc (min D.tau t) (max D.tau t) := by
    simpa [Set.uIcc] using hx
  rcases ht with ⟨htl, htr⟩
  have hmin : D.tau - D.r ≤ min D.tau t := by
    refine le_min ?_ htl
    linarith [D.hr]
  have hmax : max D.tau t ≤ D.tau + D.r := by
    refine max_le ?_ htr
    linarith [D.hr]
  exact ⟨le_trans hmin hx'.1, le_trans hx'.2 hmax⟩

private lemma drift_formula_of_zero (D : XiResolutionRecursionZeroDriftData) {t : ℝ}
    (ht : t ∈ xiShadowWindow D.tau D.r) (hzero : D.fNext t = 0) :
    ∃ ξ ∈ Set.uIcc D.tau t, t - D.tau = -D.perturb D.tau / deriv D.fNext ξ := by
  by_cases hteq : t = D.tau
  · refine ⟨D.tau, ?_, ?_⟩
    · simpa [hteq, Set.uIcc]
    · have hzero_tau : D.fNext D.tau = 0 := by simpa [hteq] using hzero
      have hperturb_zero : D.perturb D.tau = 0 := by
        simpa [next_at_tau_eq_perturb D] using hzero_tau
      simp [hteq, hperturb_zero]
  · rcases lt_or_gt_of_ne hteq with hlt | hgt
    · have hcont :
          ContinuousOn D.fNext (Set.Icc t D.tau) := by
        refine D.continuous_next.mono ?_
        intro x hx
        rcases ht with ⟨htl, _⟩
        exact ⟨le_trans htl hx.1, by linarith [D.hr, hx.2]⟩
      have hdiff :
          DifferentiableOn ℝ D.fNext (Set.Ioo t D.tau) := by
        refine D.differentiable_next.mono ?_
        intro x hx
        rcases ht with ⟨htl, _⟩
        exact ⟨le_trans htl hx.1.le, by linarith [D.hr, hx.2]⟩
      obtain ⟨ξ, hξ, hderiv⟩ := exists_deriv_eq_slope D.fNext hlt hcont hdiff
      have hξwindow : ξ ∈ xiShadowWindow D.tau D.r := by
        rcases ht with ⟨htl, _⟩
        exact ⟨le_trans htl hξ.1.le, by linarith [D.hr, hξ.2]⟩
      have hderiv_ne : deriv D.fNext ξ ≠ 0 := by
        intro h0
        have hmle : D.m ≤ 0 := by simpa [h0] using D.deriv_lower ξ hξwindow
        linarith [D.hm]
      have hslope :
          deriv D.fNext ξ * (t - D.tau) = -D.perturb D.tau := by
        have hslope' : deriv D.fNext ξ * (D.tau - t) = D.fNext D.tau - D.fNext t := by
          exact (eq_div_iff (sub_ne_zero.mpr hlt.ne')).1 hderiv
        have hslope'' : deriv D.fNext ξ * (D.tau - t) = D.perturb D.tau := by
          simpa [hzero, next_at_tau_eq_perturb D] using hslope'
        linarith
      refine ⟨ξ, ?_, ?_⟩
      · rw [Set.uIcc, min_eq_right hlt.le, max_eq_left hlt.le]
        exact Set.Ioo_subset_Icc_self hξ
      · apply (eq_div_iff hderiv_ne).2
        simpa [mul_comm] using hslope
    · have hcont :
          ContinuousOn D.fNext (Set.Icc D.tau t) := by
        refine D.continuous_next.mono ?_
        intro x hx
        rcases ht with ⟨_, htr⟩
        exact ⟨by linarith [D.hr, hx.1], le_trans hx.2 htr⟩
      have hdiff :
          DifferentiableOn ℝ D.fNext (Set.Ioo D.tau t) := by
        refine D.differentiable_next.mono ?_
        intro x hx
        rcases ht with ⟨_, htr⟩
        exact ⟨by linarith [D.hr, hx.1], le_trans hx.2.le htr⟩
      obtain ⟨ξ, hξ, hderiv⟩ := exists_deriv_eq_slope D.fNext hgt hcont hdiff
      have hξwindow : ξ ∈ xiShadowWindow D.tau D.r := by
        rcases ht with ⟨_, htr⟩
        exact ⟨by linarith [D.hr, hξ.1], le_trans hξ.2.le htr⟩
      have hderiv_ne : deriv D.fNext ξ ≠ 0 := by
        intro h0
        have hmle : D.m ≤ 0 := by simpa [h0] using D.deriv_lower ξ hξwindow
        linarith [D.hm]
      have hslope :
          deriv D.fNext ξ * (t - D.tau) = -D.perturb D.tau := by
        have hslope' : deriv D.fNext ξ * (t - D.tau) = D.fNext t - D.fNext D.tau := by
          exact (eq_div_iff (sub_ne_zero.mpr hgt.ne')).1 hderiv
        simpa [hzero, next_at_tau_eq_perturb D] using hslope'
      refine ⟨ξ, ?_, ?_⟩
      · rw [Set.uIcc, min_eq_left hgt.le, max_eq_right hgt.le]
        exact Set.Ioo_subset_Icc_self hξ
      · apply (eq_div_iff hderiv_ne).2
        simpa [mul_comm] using hslope

private lemma drift_bound_of_zero (D : XiResolutionRecursionZeroDriftData) {t : ℝ}
    (ht : t ∈ xiShadowWindow D.tau D.r) (hzero : D.fNext t = 0) :
    |t - D.tau| ≤ D.perturbSup / D.m := by
  rcases drift_formula_of_zero D ht hzero with ⟨ξ, hξ, hformula⟩
  have hξwindow : ξ ∈ xiShadowWindow D.tau D.r := uIcc_subset_window D ht hξ
  have hmξ : D.m ≤ |deriv D.fNext ξ| := D.deriv_lower ξ hξwindow
  have hcenter : |D.perturb D.tau| ≤ D.perturbSup := D.perturb_bound D.tau (tau_mem_window D)
  calc
    |t - D.tau| = |-D.perturb D.tau| / |deriv D.fNext ξ| := by
      rw [hformula, abs_div]
    _ = |D.perturb D.tau| / |deriv D.fNext ξ| := by simp
    _ ≤ |D.perturb D.tau| / D.m := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) D.hm hmξ
    _ ≤ D.perturbSup / D.m := by
      exact div_le_div_of_nonneg_right hcenter D.hm.le

/-- A one-step resolution recursion has a unique next zero in the current shadow window, its drift
is exactly controlled by the perturbation through a mean-value derivative, and the drift is bounded
by the perturbation sup norm divided by the derivative floor.
    prop:xi-resolution-recursion-zero-drift -/
theorem paper_xi_resolution_recursion_zero_drift (D : XiResolutionRecursionZeroDriftData) :
    D.nextZeroExistsUnique ∧ D.nextZeroDriftIdentity ∧ D.nextZeroDriftBound := by
  have hExistsUnique : D.nextZeroExistsUnique := by
    have hwindow_nonempty : D.tau - D.r ≤ D.tau + D.r := by linarith [D.hr]
    have hzero_mem : (0 : ℝ) ∈ D.fNext '' xiShadowWindow D.tau D.r := by
      have hIVT :=
        intermediate_value_Icc hwindow_nonempty D.continuous_next ⟨D.left_nonpos, D.right_nonneg⟩
      simpa [xiShadowWindow] using hIVT
    rcases hzero_mem with ⟨t, ht, hzero⟩
    refine ⟨t, ⟨ht, hzero⟩, ?_⟩
    intro y hy
    exact D.strictMono_next.injOn hy.1 ht (by simpa [hy.2, hzero])
  have hIdentity : D.nextZeroDriftIdentity := by
    rcases hExistsUnique with ⟨t, ht, _⟩
    rcases drift_formula_of_zero D ht.1 ht.2 with ⟨ξ, hξ, hformula⟩
    exact ⟨t, ht.1, ht.2, ξ, hξ, hformula⟩
  have hBound : D.nextZeroDriftBound := by
    intro t ht hzero
    exact drift_bound_of_zero D ht hzero
  exact ⟨hExistsUnique, hIdentity, hBound⟩

end Omega.Zeta
