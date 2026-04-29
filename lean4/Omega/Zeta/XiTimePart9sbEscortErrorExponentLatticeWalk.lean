import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9sbEscortChernoffSaddle

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete Bernoulli limit experiment for the two-temperature escort error exponent and
log-likelihood lattice walk. -/
structure xi_time_part9sb_escort_error_exponent_lattice_walk_Data where
  a : ℝ
  b : ℝ
  p : ℝ
  q : ℝ
  hb : 0 < b
  hpq : p < q
  thetaP_pos : 0 < xiTimePart9sbTheta a b p
  thetaP_lt_one : xiTimePart9sbTheta a b p < 1
  thetaQ_pos : 0 < xiTimePart9sbTheta a b q
  thetaQ_lt_one : xiTimePart9sbTheta a b q < 1
  logStep_ne_zero :
    Real.log (xiTimePart9sbTheta a b q / xiTimePart9sbTheta a b p) ≠
      Real.log ((1 - xiTimePart9sbTheta a b q) / (1 - xiTimePart9sbTheta a b p))

namespace xi_time_part9sb_escort_error_exponent_lattice_walk_Data

/-- The success probability at the left endpoint. -/
def thetaP (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : ℝ :=
  xiTimePart9sbTheta D.a D.b D.p

/-- The success probability at the right endpoint. -/
def thetaQ (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : ℝ :=
  xiTimePart9sbTheta D.a D.b D.q

/-- Log-likelihood increment when the Bernoulli observation is `1`. -/
def highStep (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : ℝ :=
  Real.log (D.thetaQ / D.thetaP)

/-- Log-likelihood increment when the Bernoulli observation is `0`. -/
def lowStep (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : ℝ :=
  Real.log ((1 - D.thetaQ) / (1 - D.thetaP))

/-- The one-step log-likelihood increment. -/
def logLikelihoodStep
    (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) (B : Bool) : ℝ :=
  if B then D.highStep else D.lowStep

/-- Number of successes in a finite Bernoulli path. -/
def successCount : List Bool → ℕ
  | [] => 0
  | true :: xs => successCount xs + 1
  | false :: xs => successCount xs

/-- Sum of one-step log-likelihood increments along a finite Bernoulli path. -/
def logLikelihoodSum
    (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : List Bool → ℝ
  | [] => 0
  | x :: xs => D.logLikelihoodStep x + D.logLikelihoodSum xs

/-- The affine lattice point selected by a path length and success count. -/
def affineLatticePoint
    (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) (n k : ℕ) : ℝ :=
  (n : ℝ) * D.lowStep + (k : ℝ) * (D.highStep - D.lowStep)

/-- Mean of the one-step log-likelihood under the right endpoint Bernoulli law. -/
def logLikelihoodMean (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : ℝ :=
  D.thetaQ * D.highStep + (1 - D.thetaQ) * D.lowStep

/-- Bernoulli KL divergence from the right endpoint to the left endpoint. -/
def bernoulliKL (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : ℝ :=
  D.thetaQ * Real.log (D.thetaQ / D.thetaP) +
    (1 - D.thetaQ) * Real.log ((1 - D.thetaQ) / (1 - D.thetaP))

/-- Variance of the two-point log-likelihood increment under the right endpoint Bernoulli law. -/
def logLikelihoodVariance (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : ℝ :=
  D.thetaQ * (D.highStep - D.logLikelihoodMean) ^ 2 +
    (1 - D.thetaQ) * (D.lowStep - D.logLikelihoodMean) ^ 2

/-- Concrete statement of the Bernoulli error exponent and affine lattice-walk calculation. -/
def errorExponentAndLatticeWalk
    (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) : Prop :=
  xiTimePart9sbChernoffObjective D.a D.b D.p D.q (1 / 2) =
      xiTimePart9sbChernoffInfo D.b D.p D.q ∧
    Set.range D.logLikelihoodStep = ({D.lowStep, D.highStep} : Set ℝ) ∧
    D.lowStep ≠ D.highStep ∧
    D.logLikelihoodMean = D.bernoulliKL ∧
    D.logLikelihoodVariance =
      D.thetaQ * (1 - D.thetaQ) * (D.highStep - D.lowStep) ^ 2 ∧
    ∀ xs : List Bool,
      D.logLikelihoodSum xs =
        D.affineLatticePoint xs.length (successCount xs)

end xi_time_part9sb_escort_error_exponent_lattice_walk_Data

private lemma xi_time_part9sb_escort_error_exponent_lattice_walk_two_point_variance
    (t hi lo : ℝ) :
    t * (hi - (t * hi + (1 - t) * lo)) ^ 2 +
        (1 - t) * (lo - (t * hi + (1 - t) * lo)) ^ 2 =
      t * (1 - t) * (hi - lo) ^ 2 := by
  ring

private lemma xi_time_part9sb_escort_error_exponent_lattice_walk_lattice_sum
    (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) (xs : List Bool) :
    D.logLikelihoodSum xs =
      D.affineLatticePoint xs.length
        (xi_time_part9sb_escort_error_exponent_lattice_walk_Data.successCount xs) := by
  induction xs with
  | nil =>
      simp [xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodSum,
        xi_time_part9sb_escort_error_exponent_lattice_walk_Data.affineLatticePoint,
        xi_time_part9sb_escort_error_exponent_lattice_walk_Data.successCount]
  | cons x xs ih =>
      cases x <;>
        simp [xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodSum,
          xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodStep,
          xi_time_part9sb_escort_error_exponent_lattice_walk_Data.successCount,
          xi_time_part9sb_escort_error_exponent_lattice_walk_Data.affineLatticePoint, ih] <;>
        ring

/-- Paper label: `cor:xi-time-part9sb-escort-error-exponent-lattice-walk`. In the Bernoulli
limit experiment, the Chernoff exponent is the quadratic escort value, the one-step likelihood
has exactly two values, its mean and variance are the usual two-point expressions, and every
finite path sum lies on the affine lattice indexed by the success count. -/
theorem paper_xi_time_part9sb_escort_error_exponent_lattice_walk
    (D : xi_time_part9sb_escort_error_exponent_lattice_walk_Data) :
    D.errorExponentAndLatticeWalk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (paper_xi_time_part9sb_escort_chernoff_saddle D.a D.b D.p D.q D.hb D.hpq).2.2.2.2.2
  · ext y
    constructor
    · rintro ⟨B, rfl⟩
      cases B <;>
        simp [xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodStep,
          xi_time_part9sb_escort_error_exponent_lattice_walk_Data.highStep,
          xi_time_part9sb_escort_error_exponent_lattice_walk_Data.lowStep]
    · intro hy
      rcases hy with rfl | rfl
      · exact ⟨false, by
          simp [xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodStep,
            xi_time_part9sb_escort_error_exponent_lattice_walk_Data.lowStep]⟩
      · exact ⟨true, by
          simp [xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodStep,
            xi_time_part9sb_escort_error_exponent_lattice_walk_Data.highStep]⟩
  · simpa [xi_time_part9sb_escort_error_exponent_lattice_walk_Data.highStep,
      xi_time_part9sb_escort_error_exponent_lattice_walk_Data.lowStep,
      xi_time_part9sb_escort_error_exponent_lattice_walk_Data.thetaP,
      xi_time_part9sb_escort_error_exponent_lattice_walk_Data.thetaQ] using D.logStep_ne_zero.symm
  · rfl
  · simp [xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodVariance,
      xi_time_part9sb_escort_error_exponent_lattice_walk_Data.logLikelihoodMean]
    exact xi_time_part9sb_escort_error_exponent_lattice_walk_two_point_variance
      D.thetaQ D.highStep D.lowStep
  · exact xi_time_part9sb_escort_error_exponent_lattice_walk_lattice_sum D

end

end Omega.Zeta
