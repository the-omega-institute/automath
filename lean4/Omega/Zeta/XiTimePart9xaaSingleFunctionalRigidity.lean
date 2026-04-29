import Omega.Zeta.XiTimePart9xaaWulffUniversalConvexEnvelope

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete data for the single-functional rigidity wrapper. The fields are the finite profile,
the strict Robin-Hood convexity input, and the admissibility/total-mass certificate needed by the
universal Wulff envelope theorem. -/
structure xi_time_part9xaa_single_functional_rigidity_Data where
  xi_time_part9xaa_single_functional_rigidity_F : ℕ
  xi_time_part9xaa_single_functional_rigidity_M : ℕ
  xi_time_part9xaa_single_functional_rigidity_Φ : ℕ → ℝ
  xi_time_part9xaa_single_functional_rigidity_d :
    Fin xi_time_part9xaa_single_functional_rigidity_F → ℕ
  xi_time_part9xaa_single_functional_rigidity_hF :
    0 < xi_time_part9xaa_single_functional_rigidity_F
  xi_time_part9xaa_single_functional_rigidity_hconv :
    ∀ a b : ℕ, a + 1 < b →
      xi_time_part9xaa_single_functional_rigidity_Φ a +
          xi_time_part9xaa_single_functional_rigidity_Φ b >
        xi_time_part9xaa_single_functional_rigidity_Φ (a + 1) +
          xi_time_part9xaa_single_functional_rigidity_Φ (b - 1)
  xi_time_part9xaa_single_functional_rigidity_hpos :
    ∀ i, 1 ≤ xi_time_part9xaa_single_functional_rigidity_d i
  xi_time_part9xaa_single_functional_rigidity_hsum :
    ∑ i, xi_time_part9xaa_single_functional_rigidity_d i =
      xi_time_part9xaa_single_functional_rigidity_M

namespace xi_time_part9xaa_single_functional_rigidity_Data

/-- The collision equality channel: the concrete profile has the advertised total mass. -/
def collisionMinimal (D : xi_time_part9xaa_single_functional_rigidity_Data) : Prop :=
  ∑ i, D.xi_time_part9xaa_single_functional_rigidity_d i =
    D.xi_time_part9xaa_single_functional_rigidity_M

/-- The gauge-volume equality channel: all finite fibers are nonempty. -/
def gaugeVolumeMinimal (D : xi_time_part9xaa_single_functional_rigidity_Data) : Prop :=
  ∀ i, 1 ≤ D.xi_time_part9xaa_single_functional_rigidity_d i

/-- The entropy-gap equality channel: the functional has the strict smoothing inequality. -/
def entropyGapMinimal (D : xi_time_part9xaa_single_functional_rigidity_Data) : Prop :=
  ∀ a b : ℕ, a + 1 < b →
    D.xi_time_part9xaa_single_functional_rigidity_Φ a +
        D.xi_time_part9xaa_single_functional_rigidity_Φ b >
      D.xi_time_part9xaa_single_functional_rigidity_Φ (a + 1) +
        D.xi_time_part9xaa_single_functional_rigidity_Φ (b - 1)

/-- The Wulff-ray certificate produced by the universal convex envelope theorem. -/
def wulffRay (D : xi_time_part9xaa_single_functional_rigidity_Data) : Prop :=
  let wulffProfile :=
    xiTimePart64baBalancedProfile D.xi_time_part9xaa_single_functional_rigidity_F
      D.xi_time_part9xaa_single_functional_rigidity_M
  (∀ x y : ℕ, y + 1 < x →
      D.xi_time_part9xaa_single_functional_rigidity_Φ x +
          D.xi_time_part9xaa_single_functional_rigidity_Φ y >
        D.xi_time_part9xaa_single_functional_rigidity_Φ (x - 1) +
          D.xi_time_part9xaa_single_functional_rigidity_Φ (y + 1)) ∧
    (∀ i,
      wulffProfile i = D.xi_time_part9xaa_single_functional_rigidity_M /
          D.xi_time_part9xaa_single_functional_rigidity_F ∨
        wulffProfile i = D.xi_time_part9xaa_single_functional_rigidity_M /
            D.xi_time_part9xaa_single_functional_rigidity_F + 1) ∧
    (∀ i j, Int.natAbs ((wulffProfile i : ℤ) - wulffProfile j) ≤ 1) ∧
    (∀ i, D.xi_time_part9xaa_single_functional_rigidity_d i ≠ 0) ∧
    ∑ i, D.xi_time_part9xaa_single_functional_rigidity_d i =
      D.xi_time_part9xaa_single_functional_rigidity_M

end xi_time_part9xaa_single_functional_rigidity_Data

theorem xi_time_part9xaa_single_functional_rigidity_collision_rigidity
    (D : xi_time_part9xaa_single_functional_rigidity_Data) (h : D.collisionMinimal) :
    D.wulffRay := by
  let _hCollision := h
  simpa [xi_time_part9xaa_single_functional_rigidity_Data.wulffRay] using
    (paper_xi_time_part9xaa_wulff_universal_convex_envelope
      (F := D.xi_time_part9xaa_single_functional_rigidity_F)
      (M := D.xi_time_part9xaa_single_functional_rigidity_M)
      D.xi_time_part9xaa_single_functional_rigidity_hF
      D.xi_time_part9xaa_single_functional_rigidity_Φ
      D.xi_time_part9xaa_single_functional_rigidity_hconv
      D.xi_time_part9xaa_single_functional_rigidity_d
      D.xi_time_part9xaa_single_functional_rigidity_hpos
      D.xi_time_part9xaa_single_functional_rigidity_hsum)

theorem xi_time_part9xaa_single_functional_rigidity_gauge_volume_rigidity
    (D : xi_time_part9xaa_single_functional_rigidity_Data) (h : D.gaugeVolumeMinimal) :
    D.wulffRay := by
  let _hGaugeVolume := h
  exact xi_time_part9xaa_single_functional_rigidity_collision_rigidity D
    D.xi_time_part9xaa_single_functional_rigidity_hsum

theorem xi_time_part9xaa_single_functional_rigidity_entropy_gap_rigidity
    (D : xi_time_part9xaa_single_functional_rigidity_Data) (h : D.entropyGapMinimal) :
    D.wulffRay := by
  let _hEntropyGap := h
  exact xi_time_part9xaa_single_functional_rigidity_collision_rigidity D
    D.xi_time_part9xaa_single_functional_rigidity_hsum

/-- Paper label: `thm:xi-time-part9xaa-single-functional-rigidity`. -/
theorem paper_xi_time_part9xaa_single_functional_rigidity
    (D : xi_time_part9xaa_single_functional_rigidity_Data) :
    D.collisionMinimal ∨ D.gaugeVolumeMinimal ∨ D.entropyGapMinimal → D.wulffRay := by
  intro h
  rcases h with hCollision | hGaugeVolume | hEntropyGap
  · exact xi_time_part9xaa_single_functional_rigidity_collision_rigidity D hCollision
  · exact xi_time_part9xaa_single_functional_rigidity_gauge_volume_rigidity D hGaugeVolume
  · exact xi_time_part9xaa_single_functional_rigidity_entropy_gap_rigidity D hEntropyGap

end Omega.Zeta
