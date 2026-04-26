import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite Jensen data for the cross-scale exclusion-radius inequality. The defect is a
finite weighted sum of positive-part functions in the logarithmic radius coordinate. -/
structure XiJensenExclusionRadiusConcavityCrossscaleData where
  ι : Type*
  instFintype : Fintype ι
  instDecidableEq : DecidableEq ι
  weight : ι → ℝ
  breakpoint : ι → ℝ
  uLeft : ℝ
  uRight : ℝ
  theta : ℝ
  hweight : ∀ i, 0 ≤ weight i
  htheta_nonneg : 0 ≤ theta
  htheta_le_one : theta ≤ 1

attribute [instance] XiJensenExclusionRadiusConcavityCrossscaleData.instFintype
attribute [instance] XiJensenExclusionRadiusConcavityCrossscaleData.instDecidableEq

namespace XiJensenExclusionRadiusConcavityCrossscaleData

/-- Positive-part notation in log-radius coordinates. -/
def xi_jensen_exclusion_radius_concavity_crossscale_positivePart (u : ℝ) : ℝ :=
  max u 0

/-- The finite Jensen defect written in log-radius coordinates. -/
def xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) (u : ℝ) : ℝ :=
  ∑ i, D.weight i *
    xi_jensen_exclusion_radius_concavity_crossscale_positivePart (u - D.breakpoint i)

/-- The concave profile `Φ(u) = u - D_F(e^u)`. -/
def xi_jensen_exclusion_radius_concavity_crossscale_phi
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) (u : ℝ) : ℝ :=
  u - xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D u

/-- The exclusion radius attached to the concave profile. -/
noncomputable def xi_jensen_exclusion_radius_concavity_crossscale_exclusionRadius
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) (u : ℝ) : ℝ :=
  Real.exp (xi_jensen_exclusion_radius_concavity_crossscale_phi D u)

/-- The logarithmic interpolation point corresponding to the multiplicative scale interpolation. -/
def xi_jensen_exclusion_radius_concavity_crossscale_mix
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) : ℝ :=
  D.theta * D.uLeft + (1 - D.theta) * D.uRight

/-- Paper-facing package: the defect is the advertised sum of positive parts, that sum is convex in
the logarithmic radius, the profile `Φ` is concave, and exponentiating yields the multiplicative
cross-scale bound for the exclusion radius. -/
def statement (D : XiJensenExclusionRadiusConcavityCrossscaleData) : Prop :=
  D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect
      D.xi_jensen_exclusion_radius_concavity_crossscale_mix =
    ∑ i, D.weight i *
      xi_jensen_exclusion_radius_concavity_crossscale_positivePart
        (D.xi_jensen_exclusion_radius_concavity_crossscale_mix - D.breakpoint i) ∧
    D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect
        D.xi_jensen_exclusion_radius_concavity_crossscale_mix ≤
      D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uLeft +
        (1 - D.theta) *
          D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uRight ∧
    D.xi_jensen_exclusion_radius_concavity_crossscale_phi
        D.xi_jensen_exclusion_radius_concavity_crossscale_mix ≥
      D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uLeft +
        (1 - D.theta) * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uRight ∧
    D.xi_jensen_exclusion_radius_concavity_crossscale_exclusionRadius
        D.xi_jensen_exclusion_radius_concavity_crossscale_mix ≥
      Real.exp (D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uLeft) *
        Real.exp ((1 - D.theta) * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uRight)

lemma xi_jensen_exclusion_radius_concavity_crossscale_positivePart_convex
    (a b theta : ℝ) (htheta_nonneg : 0 ≤ theta) (htheta_le_one : theta ≤ 1) :
    xi_jensen_exclusion_radius_concavity_crossscale_positivePart
        (theta * a + (1 - theta) * b) ≤
      theta * xi_jensen_exclusion_radius_concavity_crossscale_positivePart a +
        (1 - theta) * xi_jensen_exclusion_radius_concavity_crossscale_positivePart b := by
  unfold xi_jensen_exclusion_radius_concavity_crossscale_positivePart
  refine max_le ?_ ?_
  · have hleft : theta * a ≤ theta * max a 0 := by
      exact mul_le_mul_of_nonneg_left (le_max_left a 0) htheta_nonneg
    have htheta'_nonneg : 0 ≤ 1 - theta := sub_nonneg.mpr htheta_le_one
    have hright : (1 - theta) * b ≤ (1 - theta) * max b 0 := by
      exact mul_le_mul_of_nonneg_left (le_max_left b 0) htheta'_nonneg
    linarith
  · have htheta'_nonneg : 0 ≤ 1 - theta := sub_nonneg.mpr htheta_le_one
    have hleft_nonneg : 0 ≤ theta * max a 0 := by
      exact mul_nonneg htheta_nonneg (le_max_right a 0)
    have hright_nonneg : 0 ≤ (1 - theta) * max b 0 := by
      exact mul_nonneg htheta'_nonneg (le_max_right b 0)
    linarith

lemma xi_jensen_exclusion_radius_concavity_crossscale_term_convex
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) (i : D.ι) :
    D.weight i *
        xi_jensen_exclusion_radius_concavity_crossscale_positivePart
          (D.xi_jensen_exclusion_radius_concavity_crossscale_mix - D.breakpoint i) ≤
      D.weight i *
          (D.theta *
              xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                (D.uLeft - D.breakpoint i) +
            (1 - D.theta) *
              xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                (D.uRight - D.breakpoint i)) := by
  have hmix :
      D.xi_jensen_exclusion_radius_concavity_crossscale_mix - D.breakpoint i =
        D.theta * (D.uLeft - D.breakpoint i) +
          (1 - D.theta) * (D.uRight - D.breakpoint i) := by
    dsimp [xi_jensen_exclusion_radius_concavity_crossscale_mix]
    ring
  have hconv :=
    xi_jensen_exclusion_radius_concavity_crossscale_positivePart_convex
      (D.uLeft - D.breakpoint i) (D.uRight - D.breakpoint i) D.theta D.htheta_nonneg
      D.htheta_le_one
  rw [hmix]
  exact mul_le_mul_of_nonneg_left hconv (D.hweight i)

lemma xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect_convex
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) :
    D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect
        D.xi_jensen_exclusion_radius_concavity_crossscale_mix ≤
      D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uLeft +
        (1 - D.theta) *
          D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uRight := by
  classical
  unfold xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect
  have hsum :
      ∑ i,
          D.weight i *
            xi_jensen_exclusion_radius_concavity_crossscale_positivePart
              (D.xi_jensen_exclusion_radius_concavity_crossscale_mix - D.breakpoint i) ≤
        ∑ i,
          D.weight i *
            (D.theta *
                xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                  (D.uLeft - D.breakpoint i) +
              (1 - D.theta) *
                xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                  (D.uRight - D.breakpoint i)) := by
    exact Finset.sum_le_sum fun i _ => D.xi_jensen_exclusion_radius_concavity_crossscale_term_convex i
  calc
    ∑ i,
        D.weight i *
          xi_jensen_exclusion_radius_concavity_crossscale_positivePart
            (D.xi_jensen_exclusion_radius_concavity_crossscale_mix - D.breakpoint i)
      ≤
        ∑ i,
          D.weight i *
            (D.theta *
                xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                  (D.uLeft - D.breakpoint i) +
              (1 - D.theta) *
                xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                  (D.uRight - D.breakpoint i)) := hsum
    _ =
        D.theta *
            ∑ i,
              D.weight i *
                xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                  (D.uLeft - D.breakpoint i) +
          (1 - D.theta) *
            ∑ i,
              D.weight i *
                xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                  (D.uRight - D.breakpoint i) := by
          calc
            ∑ i,
                D.weight i *
                  (D.theta *
                      xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                        (D.uLeft - D.breakpoint i) +
                    (1 - D.theta) *
                      xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                        (D.uRight - D.breakpoint i)) =
              ∑ i,
                (D.theta *
                    (D.weight i *
                      xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                        (D.uLeft - D.breakpoint i)) +
                  (1 - D.theta) *
                    (D.weight i *
                      xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                        (D.uRight - D.breakpoint i))) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
            _ =
                ∑ i,
                  D.theta *
                    (D.weight i *
                      xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                        (D.uLeft - D.breakpoint i)) +
                ∑ i,
                  (1 - D.theta) *
                    (D.weight i *
                      xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                        (D.uRight - D.breakpoint i)) := by
                          rw [Finset.sum_add_distrib]
            _ =
                D.theta *
                    ∑ i,
                      D.weight i *
                        xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                          (D.uLeft - D.breakpoint i) +
                  (1 - D.theta) *
                    ∑ i,
                      D.weight i *
                        xi_jensen_exclusion_radius_concavity_crossscale_positivePart
                          (D.uRight - D.breakpoint i) := by
                            rw [Finset.mul_sum, Finset.mul_sum]

lemma xi_jensen_exclusion_radius_concavity_crossscale_phi_concave
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) :
    D.xi_jensen_exclusion_radius_concavity_crossscale_phi
        D.xi_jensen_exclusion_radius_concavity_crossscale_mix ≥
      D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uLeft +
        (1 - D.theta) * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uRight := by
  have hconv := D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect_convex
  have hsub :
      D.xi_jensen_exclusion_radius_concavity_crossscale_mix -
          (D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uLeft +
            (1 - D.theta) *
              D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uRight) ≤
        D.xi_jensen_exclusion_radius_concavity_crossscale_mix -
          D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect
            D.xi_jensen_exclusion_radius_concavity_crossscale_mix := by
    exact sub_le_sub_left hconv D.xi_jensen_exclusion_radius_concavity_crossscale_mix
  have hrewrite :
      D.xi_jensen_exclusion_radius_concavity_crossscale_mix -
          (D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uLeft +
            (1 - D.theta) *
              D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uRight) =
        D.theta *
            (D.uLeft - D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uLeft) +
          (1 - D.theta) *
            (D.uRight - D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect D.uRight) := by
    dsimp [xi_jensen_exclusion_radius_concavity_crossscale_mix]
    ring
  simpa [xi_jensen_exclusion_radius_concavity_crossscale_phi, hrewrite] using hsub

lemma xi_jensen_exclusion_radius_concavity_crossscale_exclusionRadius_crossscale
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) :
    D.xi_jensen_exclusion_radius_concavity_crossscale_exclusionRadius
        D.xi_jensen_exclusion_radius_concavity_crossscale_mix ≥
      Real.exp (D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uLeft) *
        Real.exp ((1 - D.theta) * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uRight) := by
  have hphi := D.xi_jensen_exclusion_radius_concavity_crossscale_phi_concave
  have hexp :
      Real.exp (D.theta * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uLeft +
          (1 - D.theta) * D.xi_jensen_exclusion_radius_concavity_crossscale_phi D.uRight) ≤
        Real.exp
          (D.xi_jensen_exclusion_radius_concavity_crossscale_phi
            D.xi_jensen_exclusion_radius_concavity_crossscale_mix) := by
    exact Real.exp_le_exp.mpr hphi
  simpa [xi_jensen_exclusion_radius_concavity_crossscale_exclusionRadius, Real.exp_add] using hexp

end XiJensenExclusionRadiusConcavityCrossscaleData

open XiJensenExclusionRadiusConcavityCrossscaleData

/-- Paper label: `thm:xi-jensen-exclusion-radius-concavity-crossscale`. -/
theorem paper_xi_jensen_exclusion_radius_concavity_crossscale
    (D : XiJensenExclusionRadiusConcavityCrossscaleData) : D.statement := by
  refine ⟨rfl, D.xi_jensen_exclusion_radius_concavity_crossscale_logJensenDefect_convex,
    D.xi_jensen_exclusion_radius_concavity_crossscale_phi_concave,
    D.xi_jensen_exclusion_radius_concavity_crossscale_exclusionRadius_crossscale⟩

end Omega.Zeta
