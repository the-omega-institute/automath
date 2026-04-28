import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zWindow6IsolatedSiteAnnihilation

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Concrete finite sitewise lift data for complete visibility of distinct-point products.  The
visible configuration fixes one finite hidden fiber over every audited site, and `localObservable`
is the local hidden observable placed at that site. -/
structure xi_time_part9z_window6_distinct_point_complete_visibility_data where
  Site : Type
  Visible : Type
  Fiber : Visible → Type
  siteFintype : Fintype Site
  siteDecidableEq : DecidableEq Site
  fiberFintype : ∀ v : Visible, Fintype (Fiber v)
  fiberNonempty : ∀ v : Visible, Nonempty (Fiber v)
  n : ℕ
  siteAt : Fin n → Site
  distinctSites : Function.Injective siteAt
  visibleConfig : Site → Visible
  localObservable : (j : Fin n) → (Σ v : Visible, Fiber v) → ℝ

namespace xi_time_part9z_window6_distinct_point_complete_visibility_data

/-- The visible label at the `j`-th audited site. -/
def xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) (j : Fin D.n) :
    D.Visible :=
  D.visibleConfig (D.siteAt j)

/-- Sum of a local observable over the hidden fiber above its visible site. -/
noncomputable def xi_time_part9z_window6_distinct_point_complete_visibility_localFiberSum
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) (j : Fin D.n) :
    ℝ := by
  let v := D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j
  exact
    (@Finset.univ (D.Fiber v) (D.fiberFintype v)).sum
      (fun u => D.localObservable j ⟨v, u⟩)

/-- Fiber mean of the local observable at the `j`-th visible site. -/
noncomputable def xi_time_part9z_window6_distinct_point_complete_visibility_visibleMean
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) (j : Fin D.n) :
    ℝ := by
  let v := D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j
  letI := D.fiberFintype v
  exact
    D.xi_time_part9z_window6_distinct_point_complete_visibility_localFiberSum j /
      (Fintype.card (D.Fiber v) : ℝ)

/-- Raw hidden product sum over the independent sitewise fibers. -/
noncomputable def xi_time_part9z_window6_distinct_point_complete_visibility_hiddenProductSum
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) : ℝ := by
  letI : (j : Fin D.n) →
      Fintype (D.Fiber
        (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j)) :=
    fun j => D.fiberFintype
      (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j)
  exact
    ∑ η : (j : Fin D.n) →
        D.Fiber (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j),
      ∏ j : Fin D.n,
        D.localObservable j
          ⟨D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j, η j⟩

/-- Normalized hidden expectation under the sitewise uniform lift. -/
noncomputable def xi_time_part9z_window6_distinct_point_complete_visibility_hiddenExpectation
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) : ℝ := by
  letI : (j : Fin D.n) →
      Fintype (D.Fiber
        (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j)) :=
    fun j => D.fiberFintype
      (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j)
  exact
    D.xi_time_part9z_window6_distinct_point_complete_visibility_hiddenProductSum /
      ∏ j : Fin D.n,
        (Fintype.card
          (D.Fiber
            (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j)) : ℝ)

/-- Paper-facing complete-visibility statement: after fiber averaging, the distinct-site hidden
product equals the product of its visible fiber means. -/
def xi_time_part9z_window6_distinct_point_complete_visibility_statement
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) : Prop :=
  D.xi_time_part9z_window6_distinct_point_complete_visibility_hiddenExpectation =
    ∏ j : Fin D.n,
      D.xi_time_part9z_window6_distinct_point_complete_visibility_visibleMean j

end xi_time_part9z_window6_distinct_point_complete_visibility_data

lemma xi_time_part9z_window6_distinct_point_complete_visibility_hiddenProductSum_eq_prod
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) :
    D.xi_time_part9z_window6_distinct_point_complete_visibility_hiddenProductSum =
      ∏ j : Fin D.n,
        D.xi_time_part9z_window6_distinct_point_complete_visibility_localFiberSum j := by
  classical
  letI : (j : Fin D.n) →
      Fintype (D.Fiber
        (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j)) :=
    fun j => D.fiberFintype
      (D.xi_time_part9z_window6_distinct_point_complete_visibility_siteVisible j)
  simp only [
    xi_time_part9z_window6_distinct_point_complete_visibility_data.xi_time_part9z_window6_distinct_point_complete_visibility_hiddenProductSum,
    xi_time_part9z_window6_distinct_point_complete_visibility_data.xi_time_part9z_window6_distinct_point_complete_visibility_localFiberSum]
  rw [Fintype.prod_sum]

/-- Paper label: `thm:xi-time-part9z-window6-distinct-point-complete-visibility`. -/
theorem paper_xi_time_part9z_window6_distinct_point_complete_visibility
    (D : xi_time_part9z_window6_distinct_point_complete_visibility_data) :
    D.xi_time_part9z_window6_distinct_point_complete_visibility_statement := by
  classical
  unfold
    xi_time_part9z_window6_distinct_point_complete_visibility_data.xi_time_part9z_window6_distinct_point_complete_visibility_statement
    xi_time_part9z_window6_distinct_point_complete_visibility_data.xi_time_part9z_window6_distinct_point_complete_visibility_hiddenExpectation
    xi_time_part9z_window6_distinct_point_complete_visibility_data.xi_time_part9z_window6_distinct_point_complete_visibility_visibleMean
  rw [xi_time_part9z_window6_distinct_point_complete_visibility_hiddenProductSum_eq_prod D]
  simp [Finset.prod_div_distrib]

end

end Omega.Zeta
