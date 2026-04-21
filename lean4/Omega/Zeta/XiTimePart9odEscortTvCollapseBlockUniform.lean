import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Zeta

open scoped goldenRatio

/-- The two-block collapse law with mass `θ` on the `A1` block. -/
def xiEscortBlockLaw (θ : ℝ) : Bool → ℝ
  | false => 1 - θ
  | true => θ

/-- Total-variation distance on a two-point space. -/
noncomputable def xiEscortTvDistance (p q : Bool → ℝ) : ℝ :=
  (|p false - q false| + |p true - q true|) / 2

/-- The exponential rate appearing in the escort-collapse estimate. -/
noncomputable def xiEscortCollapseRate (m : ℕ) : ℝ :=
  (Real.goldenRatio / 2) ^ m

/-- The exact block-uniform law with the finite-scale block weight `θ_m`. -/
def xiEscortExactBlockLaw (theta_m : ℕ → ℝ) (m : ℕ) : Bool → ℝ :=
  xiEscortBlockLaw (theta_m m)

/-- Paper-facing total-variation collapse statement. -/
def xiEscortBlockUniformTvCollapse
    (π : ℕ → Bool → ℝ) (theta : ℝ) (C : ℝ) : Prop :=
  ∀ m, xiEscortTvDistance (π m) (xiEscortBlockLaw theta) ≤ C * xiEscortCollapseRate m

lemma xiEscortTvDistance_triangle (p q r : Bool → ℝ) :
    xiEscortTvDistance p r ≤ xiEscortTvDistance p q + xiEscortTvDistance q r := by
  unfold xiEscortTvDistance
  have hfalse := abs_sub_le (p false) (q false) (r false)
  have htrue := abs_sub_le (p true) (q true) (r true)
  nlinarith

lemma xiEscortTvDistance_blockLaw (a b : ℝ) :
    xiEscortTvDistance (xiEscortBlockLaw a) (xiEscortBlockLaw b) = |a - b| := by
  unfold xiEscortTvDistance xiEscortBlockLaw
  have hfalse : (1 - a) - (1 - b) = -(a - b) := by ring
  rw [hfalse, abs_neg]
  ring

/-- Two-block escort collapse follows by combining the exact block-uniform approximation with the
finite-scale block-mass convergence and then applying the triangle inequality.
    thm:xi-time-part9od-escort-tv-collapse-block-uniform -/
theorem paper_xi_time_part9od_escort_tv_collapse_block_uniform
    (π : ℕ → Bool → ℝ) (theta_m : ℕ → ℝ) (theta C1 C2 : ℝ)
    (hApprox : ∀ m,
      xiEscortTvDistance (π m) (xiEscortExactBlockLaw theta_m m) ≤ C1 * xiEscortCollapseRate m)
    (hTheta : ∀ m, |theta_m m - theta| ≤ C2 * xiEscortCollapseRate m) :
    xiEscortBlockUniformTvCollapse π theta (C1 + C2) := by
  intro m
  have hblock :
      xiEscortTvDistance (xiEscortExactBlockLaw theta_m m) (xiEscortBlockLaw theta) =
        |theta_m m - theta| := by
    simpa [xiEscortExactBlockLaw] using xiEscortTvDistance_blockLaw (theta_m m) theta
  have hsum :
      xiEscortTvDistance (π m) (xiEscortExactBlockLaw theta_m m) + |theta_m m - theta| ≤
        C1 * xiEscortCollapseRate m + C2 * xiEscortCollapseRate m := by
    exact add_le_add (hApprox m) (hTheta m)
  calc
    xiEscortTvDistance (π m) (xiEscortBlockLaw theta) ≤
        xiEscortTvDistance (π m) (xiEscortExactBlockLaw theta_m m) +
          xiEscortTvDistance (xiEscortExactBlockLaw theta_m m) (xiEscortBlockLaw theta) := by
            exact xiEscortTvDistance_triangle (π m) (xiEscortExactBlockLaw theta_m m)
              (xiEscortBlockLaw theta)
    _ = xiEscortTvDistance (π m) (xiEscortExactBlockLaw theta_m m) + |theta_m m - theta| := by
          rw [hblock]
    _ ≤ C1 * xiEscortCollapseRate m + C2 * xiEscortCollapseRate m := hsum
    _ = (C1 + C2) * xiEscortCollapseRate m := by ring

end Omega.Zeta
