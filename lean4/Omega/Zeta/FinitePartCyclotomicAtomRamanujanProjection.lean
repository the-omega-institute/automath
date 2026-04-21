import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite-window data for the Ramanujan projection of a cyclotomic atom. The sequence
`normalizedPowerSum` encodes the coefficients `u_n(M) / n`, while `primitiveRoots` records the
primitive `m`-torsion sample points used in the projection. -/
structure FinitePartCyclotomicAtomRamanujanProjectionData where
  cutoff : ℕ
  normalizedPowerSum : ℕ → ℂ
  primitiveRoots : Finset ℂ

namespace FinitePartCyclotomicAtomRamanujanProjectionData

/-- Finite Ramanujan sum attached to the primitive-root sample at frequency `n + 1`. -/
def ramanujanSum (M : FinitePartCyclotomicAtomRamanujanProjectionData) (n : ℕ) : ℂ :=
  M.primitiveRoots.sum fun ζ => ζ ^ (n + 1)

/-- Finite cyclotomic atom obtained by summing the primitive-root evaluations of the truncated
power series. -/
def cyclotomicAtom (M : FinitePartCyclotomicAtomRamanujanProjectionData) : ℂ :=
  M.primitiveRoots.sum fun ζ =>
    (Finset.range M.cutoff).sum fun n => M.normalizedPowerSum n * ζ ^ (n + 1)

/-- Finite Ramanujan projection of the same truncated coefficient sequence. -/
def ramanujanProjection (M : FinitePartCyclotomicAtomRamanujanProjectionData) : ℂ :=
  (Finset.range M.cutoff).sum fun n => M.normalizedPowerSum n * M.ramanujanSum n

/-- The truncated primitive-root average equals the corresponding Ramanujan-sum expansion. -/
def ramanujanProjectionFormula (M : FinitePartCyclotomicAtomRamanujanProjectionData) : Prop :=
  M.cyclotomicAtom = M.ramanujanProjection

end FinitePartCyclotomicAtomRamanujanProjectionData

open FinitePartCyclotomicAtomRamanujanProjectionData

private lemma ramanujan_sum_swap
    (s : Finset ℂ) (cutoff : ℕ) (a : ℕ → ℂ) :
    s.sum (fun ζ => (Finset.range cutoff).sum fun n => a n * ζ ^ (n + 1)) =
      (Finset.range cutoff).sum fun n => a n * s.sum fun ζ => ζ ^ (n + 1) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert ζ s hζ hs =>
      simp [hζ, hs, Finset.sum_add_distrib, mul_add]

/-- Paper label: `cor:finite-part-cyclotomic-atom-ramanujan-projection`. -/
theorem paper_finite_part_cyclotomic_atom_ramanujan_projection
    (M : FinitePartCyclotomicAtomRamanujanProjectionData) : M.ramanujanProjectionFormula := by
  unfold FinitePartCyclotomicAtomRamanujanProjectionData.ramanujanProjectionFormula
  unfold FinitePartCyclotomicAtomRamanujanProjectionData.cyclotomicAtom
  unfold FinitePartCyclotomicAtomRamanujanProjectionData.ramanujanProjection
  unfold FinitePartCyclotomicAtomRamanujanProjectionData.ramanujanSum
  simpa using ramanujan_sum_swap M.primitiveRoots M.cutoff M.normalizedPowerSum

end Omega.Zeta
