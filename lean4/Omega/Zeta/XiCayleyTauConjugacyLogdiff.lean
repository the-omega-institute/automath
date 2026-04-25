import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete input for the Cayley/tau conjugacy, critical-circle criterion, and log-derivative
identity. The complex point is `σ + it`, while `x` is the real variable used for the
log-derivative computation. -/
structure xi_cayley_tau_conjugacy_logdiff_data where
  sigma : ℝ
  t : ℝ
  x : ℝ
  x_mem_Ioo : 0 < x ∧ x < 1
  point_ne_zero : sigma ^ 2 + t ^ 2 ≠ 0
  point_ne_one : (1 - sigma) ^ 2 + t ^ 2 ≠ 0

namespace xi_cayley_tau_conjugacy_logdiff_data

/-- Chapter-local Cayley coordinate `τ(s) = s / (1 - s)`. -/
def xi_cayley_tau_conjugacy_logdiff_tau (s : ℂ) : ℂ :=
  s / (1 - s)

/-- The concrete point `s = σ + it`. -/
def point (D : xi_cayley_tau_conjugacy_logdiff_data) : ℂ :=
  D.sigma + D.t * Complex.I

/-- The involution `s ↦ 1 - s` becomes inversion in the Cayley coordinate. -/
def tauConjugacy (D : xi_cayley_tau_conjugacy_logdiff_data) : Prop :=
  xi_cayley_tau_conjugacy_logdiff_tau (1 - D.point) =
    (xi_cayley_tau_conjugacy_logdiff_tau D.point)⁻¹

/-- The critical line `σ = 1 / 2` is characterized by the Cayley point lying on the unit circle. -/
def unitCircleCriterion (D : xi_cayley_tau_conjugacy_logdiff_data) : Prop :=
  Complex.normSq (xi_cayley_tau_conjugacy_logdiff_tau D.point) = 1 ↔ D.sigma = 1 / 2

/-- Log-derivative of the explicit rational coordinate `x / (1 - x)`. -/
def logDerivativeIdentity (D : xi_cayley_tau_conjugacy_logdiff_data) : Prop :=
  HasDerivAt (fun y : ℝ => Real.log (y / (1 - y)))
    ((((1 - D.x) + D.x) / (1 - D.x) ^ 2) / (D.x / (1 - D.x))) D.x

end xi_cayley_tau_conjugacy_logdiff_data

private lemma xi_cayley_tau_conjugacy_logdiff_point_ne_zero
    (D : xi_cayley_tau_conjugacy_logdiff_data) : D.point ≠ 0 := by
  intro h
  have hsigma : D.sigma = 0 := by
    simpa [xi_cayley_tau_conjugacy_logdiff_data.point] using congrArg Complex.re h
  have ht : D.t = 0 := by
    simpa [xi_cayley_tau_conjugacy_logdiff_data.point] using congrArg Complex.im h
  apply D.point_ne_zero
  simp [hsigma, ht]

private lemma xi_cayley_tau_conjugacy_logdiff_one_sub_point_ne_zero
    (D : xi_cayley_tau_conjugacy_logdiff_data) : 1 - D.point ≠ 0 := by
  intro h
  have hsigma : 1 - D.sigma = 0 := by
    simpa [xi_cayley_tau_conjugacy_logdiff_data.point] using congrArg Complex.re h
  have ht : D.t = 0 := by
    simpa [xi_cayley_tau_conjugacy_logdiff_data.point] using congrArg Complex.im h
  apply D.point_ne_one
  simp [hsigma, ht]

private lemma xi_cayley_tau_conjugacy_logdiff_tau_conjugacy_proof
    (D : xi_cayley_tau_conjugacy_logdiff_data) : D.tauConjugacy := by
  unfold xi_cayley_tau_conjugacy_logdiff_data.tauConjugacy
    xi_cayley_tau_conjugacy_logdiff_data.xi_cayley_tau_conjugacy_logdiff_tau
  have hpoint : D.point ≠ 0 := xi_cayley_tau_conjugacy_logdiff_point_ne_zero D
  have hone : 1 - D.point ≠ 0 := xi_cayley_tau_conjugacy_logdiff_one_sub_point_ne_zero D
  have hdouble : 1 - (1 - D.point) = D.point := by ring
  rw [hdouble]
  field_simp [hpoint, hone]

private lemma xi_cayley_tau_conjugacy_logdiff_normsq_formula
    (D : xi_cayley_tau_conjugacy_logdiff_data) :
    Complex.normSq
        (xi_cayley_tau_conjugacy_logdiff_data.xi_cayley_tau_conjugacy_logdiff_tau D.point) =
      (D.sigma ^ 2 + D.t ^ 2) / ((1 - D.sigma) ^ 2 + D.t ^ 2) := by
  have hpoint :
      Complex.normSq D.point = D.sigma ^ 2 + D.t ^ 2 := by
    simp [xi_cayley_tau_conjugacy_logdiff_data.point, Complex.normSq_add_mul_I]
  have hone :
      Complex.normSq (1 - D.point) = (1 - D.sigma) ^ 2 + D.t ^ 2 := by
    simp [xi_cayley_tau_conjugacy_logdiff_data.point, Complex.normSq_apply]
    ring
  rw [xi_cayley_tau_conjugacy_logdiff_data.xi_cayley_tau_conjugacy_logdiff_tau, Complex.normSq_div]
  rw [hpoint, hone]

private lemma xi_cayley_tau_conjugacy_logdiff_unit_circle_proof
    (D : xi_cayley_tau_conjugacy_logdiff_data) : D.unitCircleCriterion := by
  unfold xi_cayley_tau_conjugacy_logdiff_data.unitCircleCriterion
  rw [xi_cayley_tau_conjugacy_logdiff_normsq_formula D]
  constructor
  · intro h
    have hden_ne : ((1 - D.sigma) ^ 2 + D.t ^ 2) ≠ 0 := D.point_ne_one
    have hmul := congrArg (fun r : ℝ => r * (((1 - D.sigma) ^ 2 + D.t ^ 2))) h
    simp [hden_ne] at hmul
    nlinarith
  · intro hsigma
    rw [hsigma]
    have hden_ne : ((1 - (1 / 2 : ℝ)) ^ 2 + D.t ^ 2) ≠ 0 := by simpa [hsigma] using D.point_ne_one
    field_simp [hden_ne]
    ring

private lemma xi_cayley_tau_conjugacy_logdiff_logderiv_proof
    (D : xi_cayley_tau_conjugacy_logdiff_data) : D.logDerivativeIdentity := by
  unfold xi_cayley_tau_conjugacy_logdiff_data.logDerivativeIdentity
  have hx_ne : D.x ≠ 0 := ne_of_gt D.x_mem_Ioo.1
  have hone_ne : 1 - D.x ≠ 0 := sub_ne_zero.mpr (by linarith [D.x_mem_Ioo.2])
  have hden :
      HasDerivAt (fun y : ℝ => 1 - y) (-1) D.x := by
    simpa using (hasDerivAt_const D.x 1).sub (hasDerivAt_id D.x)
  have hquot_raw :
      HasDerivAt (fun y : ℝ => y / (1 - y)) ((((1 : ℝ) * (1 - D.x)) - D.x * (-1)) / (1 - D.x) ^ 2)
        D.x :=
    (hasDerivAt_id D.x).div hden hone_ne
  have hquot :
      HasDerivAt (fun y : ℝ => y / (1 - y)) (((1 - D.x) + D.x) / (1 - D.x) ^ 2) D.x := by
    convert hquot_raw using 1
    ring_nf
  have hvalue_ne : D.x / (1 - D.x) ≠ 0 := by
    exact div_ne_zero hx_ne hone_ne
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (y / (1 - y)))
        ((((1 - D.x) + D.x) / (1 - D.x) ^ 2) / (D.x / (1 - D.x))) D.x := by
    simpa using hquot.log hvalue_ne
  exact hlog

/-- Paper label: `prop:xi-cayley-tau-conjugacy-logdiff`. The chapter-local Cayley map conjugates
the involution `s ↦ 1 - s` to inversion, the critical line becomes the unit circle, and the
explicit logarithmic derivative is the sum of the two rational poles. -/
theorem paper_xi_cayley_tau_conjugacy_logdiff (D : xi_cayley_tau_conjugacy_logdiff_data) :
    D.tauConjugacy /\ D.unitCircleCriterion /\ D.logDerivativeIdentity := by
  exact ⟨xi_cayley_tau_conjugacy_logdiff_tau_conjugacy_proof D,
    xi_cayley_tau_conjugacy_logdiff_unit_circle_proof D,
    xi_cayley_tau_conjugacy_logdiff_logderiv_proof D⟩

end

end Omega.Zeta
