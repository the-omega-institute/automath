import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The affine path weight contributing to the projective transfer iterate on the constant-one
vector. -/
def xiAffinePathWeight {n : ℕ} (offset slope : Fin (n + 1) → ℝ) (q : ℝ) (i : Fin (n + 1)) : ℝ :=
  offset i + q * slope i

/-- The projective pressure is modeled as the supremum over finitely many affine path weights. -/
def xiProjectivePressure (n : ℕ) (offset slope : Fin (n + 1) → ℝ) (q : ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (xiAffinePathWeight offset slope q)

/-- The Perron radius associated to the projective pressure. -/
noncomputable def xiPerronRadius (n : ℕ) (offset slope : Fin (n + 1) → ℝ) (q : ℝ) : ℝ :=
  Real.exp (xiProjectivePressure n offset slope q)

/-- A finite projective pressure, realized on the constant-one vector as a supremum of affine path
weights, is midpoint convex; equivalently, the associated Perron radius is midpoint log-convex.
`thm:xi-time-part50dc-projective-pressure-perron-logconvex` -/
theorem paper_xi_time_part50dc_projective_pressure_perron_logconvex
    (n : ℕ) (offset slope : Fin (n + 1) → ℝ) (q₁ q₂ : ℝ) :
    xiProjectivePressure n offset slope ((q₁ + q₂) / 2) ≤
      (xiProjectivePressure n offset slope q₁ + xiProjectivePressure n offset slope q₂) / 2 ∧
    xiPerronRadius n offset slope ((q₁ + q₂) / 2) ^ 2 ≤
      xiPerronRadius n offset slope q₁ * xiPerronRadius n offset slope q₂ := by
  have hpressure :
      xiProjectivePressure n offset slope ((q₁ + q₂) / 2) ≤
        (xiProjectivePressure n offset slope q₁ + xiProjectivePressure n offset slope q₂) / 2 := by
    unfold xiProjectivePressure
    refine Finset.sup'_le (s := Finset.univ) (H := Finset.univ_nonempty)
      (f := xiAffinePathWeight offset slope ((q₁ + q₂) / 2)) ?_
    intro i hi
    have hi₁ :
        xiAffinePathWeight offset slope q₁ i ≤
          Finset.sup' Finset.univ Finset.univ_nonempty (xiAffinePathWeight offset slope q₁) := by
      exact Finset.le_sup' (f := xiAffinePathWeight offset slope q₁) (Finset.mem_univ i)
    have hi₂ :
        xiAffinePathWeight offset slope q₂ i ≤
          Finset.sup' Finset.univ Finset.univ_nonempty (xiAffinePathWeight offset slope q₂) := by
      exact Finset.le_sup' (f := xiAffinePathWeight offset slope q₂) (Finset.mem_univ i)
    have hmid :
        xiAffinePathWeight offset slope ((q₁ + q₂) / 2) i =
          (xiAffinePathWeight offset slope q₁ i + xiAffinePathWeight offset slope q₂ i) / 2 := by
      unfold xiAffinePathWeight
      ring
    linarith
  constructor
  · exact hpressure
  · have hdouble :
        2 * xiProjectivePressure n offset slope ((q₁ + q₂) / 2) ≤
          xiProjectivePressure n offset slope q₁ + xiProjectivePressure n offset slope q₂ := by
      linarith
    calc
      xiPerronRadius n offset slope ((q₁ + q₂) / 2) ^ 2
          = Real.exp (2 * xiProjectivePressure n offset slope ((q₁ + q₂) / 2)) := by
              rw [xiPerronRadius, pow_two, ← Real.exp_add]
              ring_nf
      _ ≤ Real.exp
            (xiProjectivePressure n offset slope q₁ + xiProjectivePressure n offset slope q₂) := by
          exact Real.exp_le_exp.mpr hdouble
      _ = xiPerronRadius n offset slope q₁ * xiPerronRadius n offset slope q₂ := by
          rw [xiPerronRadius, xiPerronRadius, Real.exp_add]

end Omega.Zeta
