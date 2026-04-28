import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.Zeta.XiTimePart72aZeroSpectrumMaximalOddDivisibilityCompression

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite data for the exact inclusion-exclusion count over the maximal odd-divisibility
generators. -/
structure xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data where
  Generator : Type
  Point : Type
  generatorDecidableEq : DecidableEq Generator
  pointDecidableEq : DecidableEq Point
  maximalGenerators : Finset Generator
  zeroCoset : Generator → Finset Point
  compatible : Finset Generator → Prop
  compatibleDecidable : ∀ I, Decidable (compatible I)
  gcdWeight : Finset Generator → ℕ
  intersectionCardinality :
    ∀ (I : Finset Generator) (hI : I.Nonempty),
      (I.inf' hI zeroCoset).card =
        if compatible I then gcdWeight I else 0

namespace xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data

attribute [local instance] Classical.propDecidable

instance xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_generatorDecidableEq
    (D : xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data) :
    DecidableEq D.Generator :=
  D.generatorDecidableEq

instance xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_pointDecidableEq
    (D : xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data) :
    DecidableEq D.Point :=
  D.pointDecidableEq

/-- The maximal-family zero spectrum cardinality formula. -/
def zeroSpectrumCardinalityFormula
    (D : xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data) : Prop :=
  ((D.maximalGenerators.biUnion D.zeroCoset).card : ℤ) =
    ∑ I : D.maximalGenerators.powerset.filter (fun I => I.Nonempty),
      (-1 : ℤ) ^ (I.1.card + 1) *
        (if D.compatible I.1 then (D.gcdWeight I.1 : ℤ) else 0)

end xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data

/-- Paper label: `thm:xi-time-part72a-zero-spectrum-maximal-family-inclusion-exclusion`.  Apply
finite inclusion-exclusion to the union over the maximal generators, then replace each finite
intersection by the supplied compatibility/gcd cardinality. -/
theorem paper_xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion
    (D : xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data) :
    D.zeroSpectrumCardinalityFormula := by
  classical
  dsimp [xi_time_part72a_zero_spectrum_maximal_family_inclusion_exclusion_data.zeroSpectrumCardinalityFormula]
  calc
    ((D.maximalGenerators.biUnion D.zeroCoset).card : ℤ) =
        ∑ I : D.maximalGenerators.powerset.filter (fun I => I.Nonempty),
          (-1 : ℤ) ^ (I.1.card + 1) * (I.1.inf' (Finset.mem_filter.mp I.2).2 D.zeroCoset).card := by
      exact Finset.inclusion_exclusion_card_biUnion D.maximalGenerators D.zeroCoset
    _ = ∑ I : D.maximalGenerators.powerset.filter (fun I => I.Nonempty),
        (-1 : ℤ) ^ (I.1.card + 1) *
          (if D.compatible I.1 then (D.gcdWeight I.1 : ℤ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro I _hI
      have hnonempty : I.1.Nonempty := (Finset.mem_filter.mp I.2).2
      rw [D.intersectionCardinality I.1 hnonempty]
      by_cases hcompat : D.compatible I.1 <;> simp [hcompat]

end Omega.Zeta
