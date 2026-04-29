import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite-window data for the isolated-site annihilation identity.  A hidden state is
represented as a visible label together with a finite fiber above that label. -/
structure xi_time_part9z_window6_isolated_site_annihilation_data where
  Site : Type
  Visible : Type
  Fiber : Visible → Type
  siteFintype : Fintype Site
  siteDecidableEq : DecidableEq Site
  visibleFintype : Fintype Visible
  fiberFintype : ∀ v : Visible, Fintype (Fiber v)
  fiberNonempty : ∀ v : Visible, Nonempty (Fiber v)
  m : ℕ
  siteAt : Fin m → Site
  isolatedIndex : Fin m
  isolatedUnique : ∀ j : Fin m, siteAt j = siteAt isolatedIndex → j = isolatedIndex
  visibleConfig : Site → Visible
  visibleObservable : (Site → Visible) → ℝ
  remainingProduct : ℝ
  f : (Σ v : Visible, Fiber v) → ℝ

namespace xi_time_part9z_window6_isolated_site_annihilation_data

/-- Sum over a finite hidden fiber, using the fiber instance stored in the data. -/
noncomputable def xi_time_part9z_window6_isolated_site_annihilation_fiberSum
    (D : xi_time_part9z_window6_isolated_site_annihilation_data) (v : D.Visible)
    (g : D.Fiber v → ℝ) : ℝ :=
  (@Finset.univ (D.Fiber v) (D.fiberFintype v)).sum g

/-- Fiber average of an observable over the hidden fiber above a visible state. -/
noncomputable def xi_time_part9z_window6_isolated_site_annihilation_fiberMean
    (D : xi_time_part9z_window6_isolated_site_annihilation_data) (v : D.Visible) : ℝ := by
  classical
  exact
    D.xi_time_part9z_window6_isolated_site_annihilation_fiberSum v
        (fun u => D.f ⟨v, u⟩) /
      @Fintype.card (D.Fiber v) (D.fiberFintype v)

/-- Centered hidden observable, with its visible-fiber mean removed. -/
noncomputable def xi_time_part9z_window6_isolated_site_annihilation_centered
    (D : xi_time_part9z_window6_isolated_site_annihilation_data)
    (n : Σ v : D.Visible, D.Fiber v) : ℝ :=
  D.f n - D.xi_time_part9z_window6_isolated_site_annihilation_fiberMean n.1

/-- Paper-facing finite-fiber annihilation statement after the visible coordinates and all other
hidden coordinates have been factored out. -/
noncomputable def xi_time_part9z_window6_isolated_site_annihilation_statement
    (D : xi_time_part9z_window6_isolated_site_annihilation_data) : Prop := by
  classical
  let v := D.visibleConfig (D.siteAt D.isolatedIndex)
  exact
    D.xi_time_part9z_window6_isolated_site_annihilation_fiberSum v (fun u =>
        D.xi_time_part9z_window6_isolated_site_annihilation_centered ⟨v, u⟩ *
          (D.visibleObservable D.visibleConfig * D.remainingProduct)) = 0

end xi_time_part9z_window6_isolated_site_annihilation_data

lemma xi_time_part9z_window6_isolated_site_annihilation_centered_fiber_sum_zero
    (D : xi_time_part9z_window6_isolated_site_annihilation_data) (v : D.Visible) :
    D.xi_time_part9z_window6_isolated_site_annihilation_fiberSum v
        (fun u => D.xi_time_part9z_window6_isolated_site_annihilation_centered ⟨v, u⟩) =
      0 := by
  classical
  letI := D.fiberFintype v
  haveI := D.fiberNonempty v
  have hcard_ne : (@Fintype.card (D.Fiber v) (D.fiberFintype v) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (D.Fiber v) ≠ 0)
  simp only [
    xi_time_part9z_window6_isolated_site_annihilation_data.xi_time_part9z_window6_isolated_site_annihilation_fiberSum,
    xi_time_part9z_window6_isolated_site_annihilation_data.xi_time_part9z_window6_isolated_site_annihilation_centered,
    xi_time_part9z_window6_isolated_site_annihilation_data.xi_time_part9z_window6_isolated_site_annihilation_fiberMean,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard_ne]
  rw [Finset.card_univ]
  ring

/-- Paper label: `thm:xi-time-part9z-window6-isolated-site-annihilation`. -/
theorem paper_xi_time_part9z_window6_isolated_site_annihilation
    (D : xi_time_part9z_window6_isolated_site_annihilation_data) :
    D.xi_time_part9z_window6_isolated_site_annihilation_statement := by
  classical
  unfold xi_time_part9z_window6_isolated_site_annihilation_data.xi_time_part9z_window6_isolated_site_annihilation_statement
  unfold xi_time_part9z_window6_isolated_site_annihilation_data.xi_time_part9z_window6_isolated_site_annihilation_fiberSum
  let v := D.visibleConfig (D.siteAt D.isolatedIndex)
  letI := D.fiberFintype v
  change
    (∑ u : D.Fiber v,
        D.xi_time_part9z_window6_isolated_site_annihilation_centered ⟨v, u⟩ *
          (D.visibleObservable D.visibleConfig * D.remainingProduct)) = 0
  rw [← Finset.sum_mul]
  have hsum := xi_time_part9z_window6_isolated_site_annihilation_centered_fiber_sum_zero D v
  unfold xi_time_part9z_window6_isolated_site_annihilation_data.xi_time_part9z_window6_isolated_site_annihilation_fiberSum at hsum
  rw [hsum]
  simp

end Omega.Zeta
