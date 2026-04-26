import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Escort amplitude `A(r) = exp (a r + b r²)` for the concrete quadratic model. -/
def xiTimePart9sbA (a b r : ℝ) : ℝ :=
  Real.exp (a * r + b * r ^ 2)

/-- Log-amplitude `g(r) = log A(r)`. -/
def xiTimePart9sbPsi (a b r : ℝ) : ℝ :=
  Real.log (xiTimePart9sbA a b r)

/-- Logarithmic slope `θ(r) = g'(r)` of the quadratic escort model. -/
def xiTimePart9sbTheta (a b r : ℝ) : ℝ :=
  a + 2 * b * r

/-- The secant slope `c_{p,q}` of `g` on the interval `[p,q]`. -/
def xiTimePart9sbSecantSlope (a b p q : ℝ) : ℝ :=
  (xiTimePart9sbPsi a b q - xiTimePart9sbPsi a b p) / (q - p)

/-- The interpolated point `r_s = (1 - s) p + s q`. -/
def xiTimePart9sbPoint (p q s : ℝ) : ℝ :=
  (1 - s) * p + s * q

/-- Jensen-gap/Chernoff objective along the escort interpolation. -/
def xiTimePart9sbChernoffObjective (a b p q s : ℝ) : ℝ :=
  (1 - s) * xiTimePart9sbPsi a b p + s * xiTimePart9sbPsi a b q -
    xiTimePart9sbPsi a b (xiTimePart9sbPoint p q s)

/-- Closed Chernoff value for the quadratic escort model. -/
def xiTimePart9sbChernoffInfo (b p q : ℝ) : ℝ :=
  b * (q - p) ^ 2 / 4

lemma xiTimePart9sbPsi_eq (a b r : ℝ) : xiTimePart9sbPsi a b r = a * r + b * r ^ 2 := by
  simp [xiTimePart9sbPsi, xiTimePart9sbA]

private lemma xiTimePart9sbSecantSlope_eq (a b p q : ℝ) (hpq : p < q) :
    xiTimePart9sbSecantSlope a b p q = a + b * (p + q) := by
  have hpq' : q - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpq)
  rw [xiTimePart9sbSecantSlope, xiTimePart9sbPsi_eq, xiTimePart9sbPsi_eq]
  field_simp [hpq']
  ring

private lemma xiTimePart9sbTheta_strictMono (a b : ℝ) (hb : 0 < b) :
    ∀ ⦃r₁ r₂ : ℝ⦄, r₁ < r₂ → xiTimePart9sbTheta a b r₁ < xiTimePart9sbTheta a b r₂ := by
  intro r₁ r₂ hr
  dsimp [xiTimePart9sbTheta]
  nlinarith

private lemma xiTimePart9sbChernoffObjective_eq (a b p q s : ℝ) :
    xiTimePart9sbChernoffObjective a b p q s = b * (q - p) ^ 2 * s * (1 - s) := by
  rw [xiTimePart9sbChernoffObjective, xiTimePart9sbPsi_eq, xiTimePart9sbPsi_eq,
    xiTimePart9sbPsi_eq]
  dsimp [xiTimePart9sbPoint]
  ring

private lemma xiTimePart9sbChernoffObjective_eq_info_sub_sq (a b p q s : ℝ) :
    xiTimePart9sbChernoffObjective a b p q s =
      xiTimePart9sbChernoffInfo b p q - b * (q - p) ^ 2 * (s - 1 / 2) ^ 2 := by
  rw [xiTimePart9sbChernoffObjective_eq, xiTimePart9sbChernoffInfo]
  ring

/-- Paper label: `thm:xi-time-part9sb-escort-chernoff-saddle`. For the quadratic escort potential
`g(r) = log A(r) = a r + b r²`, the secant slope on `[p,q]` is attained at the unique midpoint
saddle, the corresponding Chernoff objective is uniquely maximized at `s = 1/2`, and the closed
value is `b (q-p)² / 4`. -/
theorem paper_xi_time_part9sb_escort_chernoff_saddle (a b p q : ℝ) (hb : 0 < b) (hpq : p < q) :
    let sStar : ℝ := 1 / 2
    let rStar := xiTimePart9sbPoint p q sStar
    let c := xiTimePart9sbSecantSlope a b p q
    xiTimePart9sbTheta a b rStar = c ∧
      (∀ r₁ r₂ : ℝ, r₁ < r₂ → xiTimePart9sbTheta a b r₁ < xiTimePart9sbTheta a b r₂) ∧
      (∀ s : ℝ, xiTimePart9sbTheta a b (xiTimePart9sbPoint p q s) = c → s = sStar) ∧
      (∀ s : ℝ,
        xiTimePart9sbChernoffObjective a b p q s ≤ xiTimePart9sbChernoffObjective a b p q sStar) ∧
      (∀ s : ℝ,
        xiTimePart9sbChernoffObjective a b p q s =
            xiTimePart9sbChernoffObjective a b p q sStar →
          s = sStar) ∧
      xiTimePart9sbChernoffObjective a b p q sStar = xiTimePart9sbChernoffInfo b p q := by
  dsimp
  have hsec : xiTimePart9sbSecantSlope a b p q = a + b * (p + q) :=
    xiTimePart9sbSecantSlope_eq a b p q hpq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsec]
    dsimp [xiTimePart9sbTheta, xiTimePart9sbPoint]
    ring
  · intro r₁ r₂ hr
    exact xiTimePart9sbTheta_strictMono a b hb hr
  · intro s hs
    rw [hsec] at hs
    dsimp [xiTimePart9sbTheta, xiTimePart9sbPoint] at hs
    have hs' : 2 * ((1 - s) * p + s * q) = p + q := by nlinarith [hs, hb]
    have hmul : (q - p) * (2 * s - 1) = 0 := by nlinarith [hs']
    have hqp_ne : q - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpq)
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact (hqp_ne hzero).elim
    · nlinarith
  · intro s
    rw [xiTimePart9sbChernoffObjective_eq_info_sub_sq,
      xiTimePart9sbChernoffObjective_eq_info_sub_sq]
    have hnonneg : 0 ≤ b * (q - p) ^ 2 * (s - 1 / 2) ^ 2 := by positivity
    nlinarith
  · intro s hs
    rw [xiTimePart9sbChernoffObjective_eq_info_sub_sq,
      xiTimePart9sbChernoffObjective_eq_info_sub_sq] at hs
    have hzero : b * (q - p) ^ 2 * (s - 1 / 2) ^ 2 = 0 := by
      nlinarith
    have hbqp_ne : b * (q - p) ^ 2 ≠ 0 := by
      have hqp_ne : q - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpq)
      positivity
    have hsq : (s - 1 / 2) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hzero with hleft | hright
      · exact (hbqp_ne hleft).elim
      · exact hright
    nlinarith
  · rw [xiTimePart9sbChernoffObjective_eq_info_sub_sq]
    ring

end

end Omega.Zeta
