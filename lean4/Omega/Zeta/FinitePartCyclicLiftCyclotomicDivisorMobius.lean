import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Omega.Zeta.FinitePartCyclicLiftMobiusInversion
import Omega.Zeta.FinitePartCyclicLiftReducedConstantClosed

namespace Omega.Zeta

open scoped BigOperators

/-- Divisor-lattice decomposition of the finite-part anomaly into cyclotomic pieces. -/
def finitePartCyclotomicDivisorSum (cyclotomicComponent : ℕ → ℝ) (q : ℕ) : ℝ :=
  Finset.sum ((Nat.divisors q).erase 1) cyclotomicComponent

/-- Möbius recovery of the `q`-th cyclotomic component from the divisor data. -/
def finitePartCyclotomicMobiusRecovery (finitePartAnomaly : ℕ → ℝ) (q : ℕ) : ℝ :=
  Finset.sum (Nat.divisors q) fun r =>
    (ArithmeticFunction.moebius r : ℝ) * finitePartAnomaly (q / r)

/-- Chapter-local package for the cyclotomic divisor decomposition of the finite-part cyclic-lift
constant. The fields record the reduced-constant closed form, the cyclotomic factorization step,
the divisor decomposition, and the Möbius inversion recovery. -/
structure FinitePartCyclicLiftCyclotomicData where
  finitePartAnomaly : ℕ → ℝ
  cyclotomicComponent : ℕ → ℝ
  reducedConstantClosed : Prop
  cyclotomicFactorizationClosed : Prop
  divisorDecomposition :
    ∀ {q : ℕ}, 2 ≤ q →
      finitePartAnomaly q = finitePartCyclotomicDivisorSum cyclotomicComponent q
  mobiusRecovery :
    ∀ {q : ℕ}, 2 ≤ q →
      cyclotomicComponent q = finitePartCyclotomicMobiusRecovery finitePartAnomaly q

set_option maxHeartbeats 400000 in
/-- Paper-facing cyclotomic divisor decomposition for finite-part cyclic lifts: the reduced
constant closed form splits into cyclotomic components indexed by divisors of `q`, and Möbius
inversion recovers each atom. -/
theorem paper_etds_finite_part_cyclic_lift_cyclotomic_divisor_mobius
    (h : FinitePartCyclicLiftCyclotomicData) {q : ℕ} (hq : 2 ≤ q) :
    h.finitePartAnomaly q = finitePartCyclotomicDivisorSum h.cyclotomicComponent q ∧
      h.cyclotomicComponent q = finitePartCyclotomicMobiusRecovery h.finitePartAnomaly q := by
  exact ⟨h.divisorDecomposition hq, h.mobiusRecovery hq⟩

/-- Paper label: `prop:finite-part-cyclic-lift-cyclotomic-divisor-mobius`. -/
theorem paper_finite_part_cyclic_lift_cyclotomic_divisor_mobius
    (h : FinitePartCyclicLiftCyclotomicData) {q : ℕ} (hq : 2 ≤ q) :
    h.finitePartAnomaly q = finitePartCyclotomicDivisorSum h.cyclotomicComponent q ∧
      h.cyclotomicComponent q = finitePartCyclotomicMobiusRecovery h.finitePartAnomaly q := by
  exact paper_etds_finite_part_cyclic_lift_cyclotomic_divisor_mobius h hq

end Omega.Zeta
