import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Two-atom signed measure coordinates for the finite Hellinger energy model. -/
abbrev xi_hellinger_energy_functional_strict_convexity_measure := ℝ × ℝ

/-- Total mass of a two-atom signed measure. -/
def xi_hellinger_energy_functional_strict_convexity_mass
    (μ : xi_hellinger_energy_functional_strict_convexity_measure) : ℝ :=
  μ.1 + μ.2

/-- Convex interpolation of two two-atom measures. -/
def xi_hellinger_energy_functional_strict_convexity_mix (t : ℝ)
    (μ ν : xi_hellinger_energy_functional_strict_convexity_measure) :
    xi_hellinger_energy_functional_strict_convexity_measure :=
  ((1 - t) * μ.1 + t * ν.1, (1 - t) * μ.2 + t * ν.2)

/-- Difference of two two-atom measures. -/
def xi_hellinger_energy_functional_strict_convexity_sub
    (ν μ : xi_hellinger_energy_functional_strict_convexity_measure) :
    xi_hellinger_energy_functional_strict_convexity_measure :=
  (ν.1 - μ.1, ν.2 - μ.2)

/-- Finite quadratic energy induced by the signed Hellinger kernel model. -/
def xi_hellinger_energy_functional_strict_convexity_energy
    (μ : xi_hellinger_energy_functional_strict_convexity_measure) : ℝ :=
  μ.1 ^ 2 + μ.2 ^ 2

/-- The zero-mass signed-measure quadratic form is nonnegative in this finite model. -/
def xi_hellinger_energy_functional_strict_convexity_signedQuadratic
    (σ : xi_hellinger_energy_functional_strict_convexity_measure) : ℝ :=
  xi_hellinger_energy_functional_strict_convexity_energy σ

/-- The unique minimizer of the quadratic energy on the affine probability line. -/
def xi_hellinger_energy_functional_strict_convexity_center :
    xi_hellinger_energy_functional_strict_convexity_measure :=
  ((1 : ℝ) / 2, (1 : ℝ) / 2)

lemma xi_hellinger_energy_functional_strict_convexity_mix_energy
    (t : ℝ) (μ ν : xi_hellinger_energy_functional_strict_convexity_measure) :
    xi_hellinger_energy_functional_strict_convexity_energy
        (xi_hellinger_energy_functional_strict_convexity_mix t μ ν) =
      (1 - t) * xi_hellinger_energy_functional_strict_convexity_energy μ +
        t * xi_hellinger_energy_functional_strict_convexity_energy ν -
          t * (1 - t) *
            xi_hellinger_energy_functional_strict_convexity_energy
              (xi_hellinger_energy_functional_strict_convexity_sub ν μ) := by
  unfold xi_hellinger_energy_functional_strict_convexity_energy
    xi_hellinger_energy_functional_strict_convexity_mix
    xi_hellinger_energy_functional_strict_convexity_sub
  ring

lemma xi_hellinger_energy_functional_strict_convexity_sub_energy_pos
    {μ ν : xi_hellinger_energy_functional_strict_convexity_measure} (hμν : μ ≠ ν) :
    0 <
      xi_hellinger_energy_functional_strict_convexity_energy
        (xi_hellinger_energy_functional_strict_convexity_sub ν μ) := by
  have hcoord : μ.1 ≠ ν.1 ∨ μ.2 ≠ ν.2 := by
    by_contra h
    push_neg at h
    apply hμν
    ext <;> simp [h.1, h.2]
  unfold xi_hellinger_energy_functional_strict_convexity_energy
    xi_hellinger_energy_functional_strict_convexity_sub
  cases hcoord with
  | inl h =>
      have hsub : ν.1 - μ.1 ≠ 0 := by
        intro hzero
        apply h
        linarith
      have hs : 0 < (ν.1 - μ.1) ^ 2 := sq_pos_of_ne_zero hsub
      nlinarith [sq_nonneg (ν.2 - μ.2)]
  | inr h =>
      have hsub : ν.2 - μ.2 ≠ 0 := by
        intro hzero
        apply h
        linarith
      have hs : 0 < (ν.2 - μ.2) ^ 2 := sq_pos_of_ne_zero hsub
      nlinarith [sq_nonneg (ν.1 - μ.1)]

/-- Concrete finite statement: the zero-mass quadratic form is nonnegative, mixture expansion
gives strict convexity on the affine probability line, and the constrained minimizer is unique. -/
def xi_hellinger_energy_functional_strict_convexity_statement : Prop :=
  (∀ σ : xi_hellinger_energy_functional_strict_convexity_measure,
    xi_hellinger_energy_functional_strict_convexity_mass σ = 0 →
      0 ≤ xi_hellinger_energy_functional_strict_convexity_signedQuadratic σ) ∧
    (∀ (μ ν : xi_hellinger_energy_functional_strict_convexity_measure) (t : ℝ),
      xi_hellinger_energy_functional_strict_convexity_mass μ = 1 →
        xi_hellinger_energy_functional_strict_convexity_mass ν = 1 →
          0 ≤ t → t ≤ 1 →
            xi_hellinger_energy_functional_strict_convexity_energy
                (xi_hellinger_energy_functional_strict_convexity_mix t μ ν) ≤
              (1 - t) * xi_hellinger_energy_functional_strict_convexity_energy μ +
                t * xi_hellinger_energy_functional_strict_convexity_energy ν) ∧
    (∀ (μ ν : xi_hellinger_energy_functional_strict_convexity_measure) (t : ℝ),
      xi_hellinger_energy_functional_strict_convexity_mass μ = 1 →
        xi_hellinger_energy_functional_strict_convexity_mass ν = 1 →
          0 < t → t < 1 → μ ≠ ν →
            xi_hellinger_energy_functional_strict_convexity_energy
                (xi_hellinger_energy_functional_strict_convexity_mix t μ ν) <
              (1 - t) * xi_hellinger_energy_functional_strict_convexity_energy μ +
                t * xi_hellinger_energy_functional_strict_convexity_energy ν) ∧
    (∀ μ : xi_hellinger_energy_functional_strict_convexity_measure,
      xi_hellinger_energy_functional_strict_convexity_mass μ = 1 →
        xi_hellinger_energy_functional_strict_convexity_energy
            xi_hellinger_energy_functional_strict_convexity_center ≤
          xi_hellinger_energy_functional_strict_convexity_energy μ ∧
        (xi_hellinger_energy_functional_strict_convexity_energy μ =
            xi_hellinger_energy_functional_strict_convexity_energy
              xi_hellinger_energy_functional_strict_convexity_center →
          μ = xi_hellinger_energy_functional_strict_convexity_center))

/-- Paper label: `prop:xi-hellinger-energy-functional-strict-convexity`. -/
theorem paper_xi_hellinger_energy_functional_strict_convexity :
    xi_hellinger_energy_functional_strict_convexity_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ _hσ
    unfold xi_hellinger_energy_functional_strict_convexity_signedQuadratic
      xi_hellinger_energy_functional_strict_convexity_energy
    nlinarith [sq_nonneg σ.1, sq_nonneg σ.2]
  · intro μ ν t _hμ _hν ht0 ht1
    rw [xi_hellinger_energy_functional_strict_convexity_mix_energy]
    have hdiff :
        0 ≤ xi_hellinger_energy_functional_strict_convexity_energy
          (xi_hellinger_energy_functional_strict_convexity_sub ν μ) := by
      unfold xi_hellinger_energy_functional_strict_convexity_energy
        xi_hellinger_energy_functional_strict_convexity_sub
      nlinarith [sq_nonneg (ν.1 - μ.1), sq_nonneg (ν.2 - μ.2)]
    have hfactor : 0 ≤ t * (1 - t) := by nlinarith
    nlinarith [mul_nonneg hfactor hdiff]
  · intro μ ν t _hμ _hν ht0 ht1 hμν
    rw [xi_hellinger_energy_functional_strict_convexity_mix_energy]
    have hfactor : 0 < t * (1 - t) := by nlinarith
    have hdiff := xi_hellinger_energy_functional_strict_convexity_sub_energy_pos hμν
    have hprod :
        0 <
          t * (1 - t) *
            xi_hellinger_energy_functional_strict_convexity_energy
              (xi_hellinger_energy_functional_strict_convexity_sub ν μ) :=
      mul_pos hfactor hdiff
    nlinarith
  · intro μ hμ
    have hsecond : μ.2 = 1 - μ.1 := by
      unfold xi_hellinger_energy_functional_strict_convexity_mass at hμ
      linarith
    have hidentity :
        xi_hellinger_energy_functional_strict_convexity_energy μ =
          (1 : ℝ) / 2 + 2 * (μ.1 - (1 : ℝ) / 2) ^ 2 := by
      unfold xi_hellinger_energy_functional_strict_convexity_energy
      rw [hsecond]
      ring
    constructor
    · rw [hidentity]
      unfold xi_hellinger_energy_functional_strict_convexity_center
        xi_hellinger_energy_functional_strict_convexity_energy
      norm_num
      nlinarith [sq_nonneg (μ.1 - (1 : ℝ) / 2)]
    · intro hmin
      have hsq : (μ.1 - (1 : ℝ) / 2) ^ 2 = 0 := by
        unfold xi_hellinger_energy_functional_strict_convexity_center
          xi_hellinger_energy_functional_strict_convexity_energy at hmin
        norm_num at hmin
        nlinarith [hidentity]
      have hfirst : μ.1 = (1 : ℝ) / 2 := by nlinarith [sq_nonneg (μ.1 - (1 : ℝ) / 2)]
      have hsecond' : μ.2 = (1 : ℝ) / 2 := by nlinarith
      ext <;> simp [xi_hellinger_energy_functional_strict_convexity_center, hfirst, hsecond']

end

end Omega.Zeta
