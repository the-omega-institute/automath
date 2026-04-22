import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedProjectivePressureSecantRigidity

namespace Omega.DerivedConsequences

private lemma derived_projective_pressure_strict_logconvex_certificate_midpoint_strict
    (tau0 tau1 c : ℝ) (hc : 0 < c) (N n : ℕ) (_hn : 0 < n) (hnN : n + 1 < N) :
    2 * derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c ((n : ℝ) / N) <
      derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c (((n - 1 : ℕ) : ℝ) / N) +
        derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c (((n + 1 : ℕ) : ℝ) / N) := by
  have hNnat : 0 < N := by
    omega
  have hN : (0 : ℝ) < N := by
    exact_mod_cast hNnat
  have hnm1 : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    norm_num
  have hnp1 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
    norm_num
  have hgap :
      derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c
          (((n - 1 : ℕ) : ℝ) / N) +
        derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c
          (((n + 1 : ℕ) : ℝ) / N) -
        2 * derived_projective_pressure_secant_rigidity_pressure tau0 tau1 c ((n : ℝ) / N) =
      2 * c / (N : ℝ) ^ 2 := by
    unfold derived_projective_pressure_secant_rigidity_pressure
      derived_projective_pressure_secant_rigidity_secant
    rw [hnm1, hnp1]
    field_simp [hN.ne']
    ring
  have hpos : 0 < 2 * c / (N : ℝ) ^ 2 := by
    positivity
  nlinarith [hgap, hpos]

/-- Paper label: `cor:derived-projective-pressure-strict-logconvex-certificate`. The strictly
convex quadratic correction forces strict midpoint convexity of the pressure at adjacent integer
anchors, and exponentiating gives the strict log-convexity inequality for the radii. -/
theorem paper_derived_projective_pressure_strict_logconvex_certificate
    (tau0 tau1 c : ℝ) (hc : 0 < c) (N n : ℕ) (hn : 0 < n) (hnN : n + 1 < N) :
    derived_projective_pressure_secant_rigidity_radius tau0 tau1 c N n ^ 2 <
      derived_projective_pressure_secant_rigidity_radius tau0 tau1 c N (n - 1) *
        derived_projective_pressure_secant_rigidity_radius tau0 tau1 c N (n + 1) := by
  have hmid :=
    derived_projective_pressure_strict_logconvex_certificate_midpoint_strict
      tau0 tau1 c hc N n hn hnN
  have hexp := Real.exp_lt_exp.mpr hmid
  simpa [derived_projective_pressure_secant_rigidity_radius, pow_two, two_mul, Real.exp_add,
    mul_assoc, mul_left_comm, mul_comm] using hexp

end Omega.DerivedConsequences
