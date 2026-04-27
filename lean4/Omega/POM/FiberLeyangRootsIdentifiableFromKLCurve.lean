import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data package for recovering a Lee--Yang root spectrum from a KL curve.

The analytic part records that the KL curve has already recovered the second derivative of the
log-partition function and fixed the permitted affine ambiguity.  The algebraic output is the
recovered partition polynomial, known up to multiplication by a nonzero scalar. -/
structure pom_fiber_leyang_roots_identifiable_from_kl_curve_data where
  logPartition : ℝ → ℝ
  recoveredLogPartition : ℝ → ℝ
  klCurve : ℝ → ℝ
  logPartitionSecondDerivative : ℝ → ℝ
  recoveredSecondDerivative : ℝ → ℝ
  klDifferentiationIdentity :
    ∀ t : ℝ, recoveredSecondDerivative t = logPartitionSecondDerivative t
  affineAmbiguity : ℝ → ℝ
  affineRecovery :
    ∀ t : ℝ, recoveredLogPartition t = logPartition t + affineAmbiguity t
  zeroSlopeFromBoundedness : affineAmbiguity 0 = 0
  partitionPolynomial : Polynomial ℂ
  recoveredPolynomial : Polynomial ℂ
  scalar : ℂ
  scalar_ne_zero : scalar ≠ 0
  recoveredPolynomial_eq : recoveredPolynomial = scalar • partitionPolynomial

namespace pom_fiber_leyang_roots_identifiable_from_kl_curve_data

/-- The root spectrum is the zero locus of the partition polynomial. -/
def rootSpectrum (D : pom_fiber_leyang_roots_identifiable_from_kl_curve_data) : Set ℂ :=
  {z | D.partitionPolynomial.eval z = 0}

/-- The recovered root spectrum is the zero locus of the recovered partition polynomial. -/
def recoveredRootSpectrum (D : pom_fiber_leyang_roots_identifiable_from_kl_curve_data) : Set ℂ :=
  {z | D.recoveredPolynomial.eval z = 0}

/-- The KL curve determines the Lee--Yang root spectrum when the recovered and original zero
loci agree. -/
def klCurveDeterminesRootSpectrum
    (D : pom_fiber_leyang_roots_identifiable_from_kl_curve_data) : Prop :=
  D.recoveredRootSpectrum = D.rootSpectrum

end pom_fiber_leyang_roots_identifiable_from_kl_curve_data

/-- Nonzero scalar multiplication does not change the zero locus of a complex polynomial. -/
lemma pom_fiber_leyang_roots_identifiable_from_kl_curve_scalar_rootSpectrum
    (D : pom_fiber_leyang_roots_identifiable_from_kl_curve_data) :
    D.recoveredRootSpectrum = D.rootSpectrum := by
  ext z
  rw [pom_fiber_leyang_roots_identifiable_from_kl_curve_data.recoveredRootSpectrum,
    pom_fiber_leyang_roots_identifiable_from_kl_curve_data.rootSpectrum]
  change D.recoveredPolynomial.eval z = 0 ↔ D.partitionPolynomial.eval z = 0
  rw [D.recoveredPolynomial_eq]
  simp [Polynomial.eval_smul, D.scalar_ne_zero]

/-- Paper label: `prop:pom-fiber-leyang-roots-identifiable-from-kl-curve`.

Once the KL curve has fixed the log-partition function up to the admissible affine ambiguity, the
resulting partition polynomial is determined up to a nonzero scalar, hence its Lee--Yang root
spectrum is unchanged. -/
theorem paper_pom_fiber_leyang_roots_identifiable_from_kl_curve
    (D : pom_fiber_leyang_roots_identifiable_from_kl_curve_data) :
    D.klCurveDeterminesRootSpectrum := by
  exact pom_fiber_leyang_roots_identifiable_from_kl_curve_scalar_rootSpectrum D

end Omega.POM
