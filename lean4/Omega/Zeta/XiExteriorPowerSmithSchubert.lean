import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The exterior-power Smith exponents attached to the staircase diagonal `0,1,…,q` are modeled as
the multiset of all `k`-subset sums. -/
noncomputable def xiExteriorPowerSmithExponentMultiset (q k : ℕ) : Multiset ℕ :=
  ((((Finset.range (q + 1)).powersetCard k).val.toList.map
      (fun S : Finset ℕ => Finset.sum S fun i => i)) : List ℕ)

/-- The Schubert shift contributed by the staircase subset `{0,1,…,k-1}`. -/
def xiExteriorPowerSchubertBase (k : ℕ) : ℕ :=
  k * (k - 1) / 2

/-- Paper label: `thm:xi-exterior-power-smith-schubert`.
For the staircase Smith diagonal `diag(π^0,…,π^q)`, the `k`-th exterior-power exponent multiset has
the expected binomial cardinality, and its Schubert base exponent is realized by the initial
`k`-subset `{0,1,…,k-1}`. -/
theorem paper_xi_exterior_power_smith_schubert (q k : ℕ) (_hq : 2 ≤ q) (_hk1 : 1 ≤ k)
    (hkq : k ≤ q + 1) :
    (xiExteriorPowerSmithExponentMultiset q k).card = Nat.choose (q + 1) k ∧
      xiExteriorPowerSchubertBase k ∈ xiExteriorPowerSmithExponentMultiset q k := by
  constructor
  · simp [xiExteriorPowerSmithExponentMultiset]
  · let subsets : List (Finset ℕ) := ((Finset.range (q + 1)).powersetCard k).toList
    have hsubset : Finset.range k ∈ subsets := by
      simp [subsets, Finset.mem_powersetCard, hkq]
    have hbase :
        Finset.sum (Finset.range k) (fun i => i) = xiExteriorPowerSchubertBase k := by
      simpa [xiExteriorPowerSchubertBase] using Finset.sum_range_id k
    have hmem :
        xiExteriorPowerSchubertBase k ∈ subsets.map (fun S : Finset ℕ => Finset.sum S fun i => i) :=
      List.mem_map.2 ⟨Finset.range k, hsubset, hbase⟩
    simpa [xiExteriorPowerSmithExponentMultiset, subsets] using hmem

end Omega.Zeta
