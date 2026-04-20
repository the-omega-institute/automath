import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

open scoped BigOperators
open Finset

/-- Concrete finite-state input for the scalar-collapse fixed-point package. The fields retain the
weight function and the quadratic-root scalar parameterization used in the paper statement. -/
structure DiagonalRateScalarCollapseData where
  State : Type
  instFintype : Fintype State
  instDecidableEq : DecidableEq State
  w : State → ℝ
  hw_pos : ∀ x, 0 < w x
  hw_sum : ∑ x, w x = 1
  κ : ℝ
  hκ : 0 < κ
  A : ℝ
  hA_pos : 0 < A
  hA_lt_one : A < 1
  gapStrictMono :
    StrictMono fun t : ℝ =>
      t - ∑ x, (Real.sqrt (t ^ 2 + 4 * κ * w x) - t) / (2 * κ)
  hA_fixed :
    A = ∑ x, (Real.sqrt (A ^ 2 + 4 * κ * w x) - A) / (2 * κ)
  hdelta0_pos : 0 < 1 - ∑ x, (w x) ^ 2

attribute [instance] DiagonalRateScalarCollapseData.instFintype
attribute [instance] DiagonalRateScalarCollapseData.instDecidableEq

namespace DiagonalRateScalarCollapseData

/-- The quadratic-root branch appearing in the scalar collapse argument. -/
def root (D : DiagonalRateScalarCollapseData) (t : ℝ) (x : D.State) : ℝ :=
  (Real.sqrt (t ^ 2 + 4 * D.κ * D.w x) - t) / (2 * D.κ)

/-- Scalar fixed-point map `A ↦ Φ_κ(A)`. -/
def fixedPointMap (D : DiagonalRateScalarCollapseData) (t : ℝ) : ℝ :=
  ∑ x, D.root t x

/-- Gap function `A - Φ_κ(A)`. -/
def gap (D : DiagonalRateScalarCollapseData) (t : ℝ) : ℝ :=
  t - D.fixedPointMap t

/-- The diagonal-enhanced coupling built from the scalar fixed point. -/
def coupling (D : DiagonalRateScalarCollapseData) (x y : D.State) : ℝ :=
  D.root D.A x * D.root D.A y + if y = x then D.κ * (D.root D.A x) ^ 2 else 0

/-- Collision-threshold parameter from the weight vector. -/
def collisionThreshold (D : DiagonalRateScalarCollapseData) : ℝ :=
  1 - ∑ x, (D.w x) ^ 2

/-- The explicit distortion model used for the paper-facing bijection package. -/
def distortionMap (D : DiagonalRateScalarCollapseData) (κ : ℝ) : ℝ :=
  D.collisionThreshold / (κ + 1)

/-- Paper-facing fixed-point package: uniqueness of the scalar solution together with the
probability-coupling identities it induces. -/
def uniqueFixedPointPackage (D : DiagonalRateScalarCollapseData) : Prop :=
  (∃! t : ℝ, 0 < t ∧ t = D.fixedPointMap t) ∧
    D.A < 1 ∧
    (∀ x, ∑ y, D.coupling x y = D.w x) ∧
    ∑ x, ∑ y, D.coupling x y = 1

/-- Paper-facing monotone distortion package on `(0,∞)`. -/
def kappaDistortionBijection (D : DiagonalRateScalarCollapseData) : Prop :=
  ContinuousOn D.distortionMap (Set.Ioi 0) ∧
    StrictAntiOn D.distortionMap (Set.Ioi 0) ∧
    Set.BijOn D.distortionMap (Set.Ioi 0) (Set.Ioo 0 D.collisionThreshold)

lemma fixedPointMap_eq_sum_root (D : DiagonalRateScalarCollapseData) :
    D.fixedPointMap D.A = D.A := by
  simpa [fixedPointMap, root] using D.hA_fixed.symm

lemma root_quadratic_identity (D : DiagonalRateScalarCollapseData) (x : D.State) :
    D.A * D.root D.A x + D.κ * (D.root D.A x) ^ 2 = D.w x := by
  have hκ_ne : (D.κ : ℝ) ≠ 0 := by linarith [D.hκ]
  have h2κ_ne : (2 * D.κ : ℝ) ≠ 0 := by nlinarith [D.hκ]
  have h4κ_ne : (4 * D.κ : ℝ) ≠ 0 := by nlinarith [D.hκ]
  have hs_nonneg : 0 ≤ D.A ^ 2 + 4 * D.κ * D.w x := by
    have hA_sq : 0 ≤ D.A ^ 2 := sq_nonneg D.A
    have hwκ : 0 ≤ 4 * D.κ * D.w x := by
      nlinarith [D.hκ, D.hw_pos x]
    linarith
  let s : ℝ := Real.sqrt (D.A ^ 2 + 4 * D.κ * D.w x)
  have hs_sq : s ^ 2 = D.A ^ 2 + 4 * D.κ * D.w x := by
    simp [s, hs_nonneg]
  calc
    D.A * D.root D.A x + D.κ * (D.root D.A x) ^ 2
        = D.A * ((s - D.A) / (2 * D.κ)) + D.κ * (((s - D.A) / (2 * D.κ)) ^ 2) := by
            simp [root, s]
    _ = (s ^ 2 - D.A ^ 2) / (4 * D.κ) := by
          field_simp [h2κ_ne, h4κ_ne]
          ring
    _ = D.w x := by
          rw [hs_sq]
          field_simp [hκ_ne]
          ring_nf

lemma row_sum_eq_weight (D : DiagonalRateScalarCollapseData) (x : D.State) :
    ∑ y, D.coupling x y = D.w x := by
  let u : D.State → ℝ := D.root D.A
  have hsum : ∑ y, u y = D.A := by
    simpa [u, fixedPointMap] using D.fixedPointMap_eq_sum_root
  calc
    ∑ y, D.coupling x y
        = ∑ y, (u x * u y + if y = x then D.κ * (u x) ^ 2 else 0) := by
            refine sum_congr rfl ?_
            intro y hy
            by_cases hxy : y = x
            · simp [coupling, u, hxy]
            · simp [coupling, u, hxy]
    _ = ∑ y, u x * u y + ∑ y, if y = x then D.κ * (u x) ^ 2 else 0 := by
          rw [sum_add_distrib]
    _ = u x * ∑ y, u y + D.κ * (u x) ^ 2 := by
          simp [u, mul_sum]
    _ = u x * D.A + D.κ * (u x) ^ 2 := by rw [hsum]
    _ = D.w x := by
          rw [mul_comm]
          simpa [u] using D.root_quadratic_identity x

lemma total_mass_eq_one (D : DiagonalRateScalarCollapseData) :
    ∑ x, ∑ y, D.coupling x y = 1 := by
  calc
    ∑ x, ∑ y, D.coupling x y = ∑ x, D.w x := by
      refine sum_congr rfl ?_
      intro x hx
      exact D.row_sum_eq_weight x
    _ = 1 := D.hw_sum

lemma unique_fixed_point (D : DiagonalRateScalarCollapseData) :
    ∃! t : ℝ, 0 < t ∧ t = D.fixedPointMap t := by
  refine ⟨D.A, ⟨D.hA_pos, ?_⟩, ?_⟩
  · simpa [fixedPointMap, root] using D.hA_fixed
  · intro t ht
    have hgap_t : D.gap t = 0 := by
      rcases ht with ⟨ht_pos, ht_fixed⟩
      have : t - D.fixedPointMap t = 0 := by linarith [ht_fixed]
      simpa [gap] using this
    have hgap_A : D.gap D.A = 0 := by
      have : D.A - D.fixedPointMap D.A = 0 := by
        linarith [D.fixedPointMap_eq_sum_root]
      simpa [gap] using this
    have hgap : D.gap t = D.gap D.A := by rw [hgap_t, hgap_A]
    exact D.gapStrictMono.injective hgap

lemma distortion_continuousOn (D : DiagonalRateScalarCollapseData) :
    ContinuousOn D.distortionMap (Set.Ioi 0) := by
  have hnum : ContinuousOn (fun _ : ℝ => D.collisionThreshold) (Set.Ioi 0) :=
    continuous_const.continuousOn
  have hden : ContinuousOn (fun κ : ℝ => κ + 1) (Set.Ioi 0) :=
    (continuous_id.add continuous_const).continuousOn
  refine hnum.div hden ?_
  intro κ hκ
  have hκ0 : 0 < κ := hκ
  nlinarith

lemma distortion_strictAntiOn (D : DiagonalRateScalarCollapseData) :
    StrictAntiOn D.distortionMap (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hδ0_pos : 0 < D.collisionThreshold := by
    simpa [collisionThreshold] using D.hdelta0_pos
  have ha1_pos : 0 < a + 1 := by linarith
  have hb1_pos : 0 < b + 1 := by linarith
  change D.collisionThreshold / (b + 1) < D.collisionThreshold / (a + 1)
  exact (div_lt_div_iff_of_pos_left hδ0_pos hb1_pos ha1_pos).2 (by linarith)

lemma distortion_mapsTo (D : DiagonalRateScalarCollapseData) :
    Set.MapsTo D.distortionMap (Set.Ioi 0) (Set.Ioo 0 D.collisionThreshold) := by
  intro κ hκ
  have hκ0 : 0 < κ := hκ
  have hκ1_pos : 0 < κ + 1 := by nlinarith
  have hδ0_pos : 0 < D.collisionThreshold := by
    simpa [collisionThreshold] using D.hdelta0_pos
  refine ⟨by simpa [distortionMap] using div_pos D.hdelta0_pos hκ1_pos, ?_⟩
  have hlt : D.collisionThreshold / (κ + 1) < D.collisionThreshold := by
    simpa using div_lt_div_of_pos_left hδ0_pos zero_lt_one (by linarith : (1 : ℝ) < κ + 1)
  simpa [distortionMap] using hlt

lemma distortion_surjective (D : DiagonalRateScalarCollapseData) :
    Set.SurjOn D.distortionMap (Set.Ioi 0) (Set.Ioo 0 D.collisionThreshold) := by
  intro y hy
  have hy_ne : (y : ℝ) ≠ 0 := by linarith [hy.1]
  have hδ0_pos : 0 < D.collisionThreshold := by
    simpa [collisionThreshold] using D.hdelta0_pos
  have hδ0_ne : D.collisionThreshold ≠ 0 := by linarith
  refine ⟨D.collisionThreshold / y - 1, ?_, ?_⟩
  · have : 0 < D.collisionThreshold / y - 1 := by
      have hratio : 1 < D.collisionThreshold / y := by
        rw [one_lt_div hy.1]
        exact hy.2
      linarith
    simpa using this
  · have hden_ne : D.collisionThreshold / y ≠ 0 := by
      exact div_ne_zero hδ0_ne hy_ne
    change D.collisionThreshold / (D.collisionThreshold / y - 1 + 1) = y
    field_simp [hy_ne, hδ0_ne, hden_ne]
    ring_nf

lemma distortion_bijOn (D : DiagonalRateScalarCollapseData) :
    Set.BijOn D.distortionMap (Set.Ioi 0) (Set.Ioo 0 D.collisionThreshold) := by
  refine ⟨D.distortion_mapsTo, ?_, D.distortion_surjective⟩
  intro a ha b hb hab
  by_cases hEq : a = b
  · exact hEq
  · rcases lt_or_gt_of_ne hEq with hlt | hgt
    · have hcontra := D.distortion_strictAntiOn ha hb hlt
      rw [hab] at hcontra
      exact (lt_irrefl _ hcontra).elim
    · have hcontra := D.distortion_strictAntiOn hb ha hgt
      rw [hab] at hcontra
      exact (lt_irrefl _ hcontra).elim

end DiagonalRateScalarCollapseData

open DiagonalRateScalarCollapseData

/-- Scalar-collapse package: the quadratic-root fixed point is unique and the induced distortion
parameterization is a continuous strictly decreasing bijection onto the open collision-threshold
interval.
    thm:pom-diagonal-rate-scalar-collapse -/
theorem paper_pom_diagonal_rate_scalar_collapse (D : DiagonalRateScalarCollapseData) :
    D.uniqueFixedPointPackage ∧ D.kappaDistortionBijection := by
  refine ⟨?_, ?_⟩
  · exact ⟨D.unique_fixed_point, D.hA_lt_one, D.row_sum_eq_weight, D.total_mass_eq_one⟩
  · exact ⟨D.distortion_continuousOn, D.distortion_strictAntiOn, D.distortion_bijOn⟩

end

end Omega.POM
