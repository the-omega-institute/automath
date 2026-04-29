import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace Omega.POM

open Filter
open scoped BigOperators

noncomputable section

/-- Concrete finite-sector data for a symmetric-group Gibbs mixture with several maximal
conjugacy-class sectors. The normalized finite-temperature weights are represented by
`normalizedWeight`; maximal sectors converge to the normalized positive weights, while
nonmaximal sectors vanish. -/
structure pom_symmetric_group_gibbs_mixture_data where
  sectorCount : ℕ
  maximalSectors : Finset (Fin sectorCount)
  weight : Fin sectorCount → ℝ
  normalizedWeight : ℕ → Fin sectorCount → ℝ
  characterValue : Fin sectorCount → ℝ
  maximal_nonempty : maximalSectors.Nonempty
  weight_pos : ∀ ν, ν ∈ maximalSectors → 0 < weight ν
  maximal_converges :
    ∀ ν, ν ∈ maximalSectors →
      Tendsto (fun m : ℕ => normalizedWeight m ν) atTop
        (nhds (weight ν / (∑ μ ∈ maximalSectors, weight μ)))
  nonmaximal_vanishes :
    ∀ ν, ν ∉ maximalSectors →
      Tendsto (fun m : ℕ => normalizedWeight m ν) atTop (nhds 0)

/-- Total positive weight carried by the maximal conjugacy-class sectors. -/
def pom_symmetric_group_gibbs_mixture_maximalWeight
    (D : pom_symmetric_group_gibbs_mixture_data) : ℝ :=
  ∑ ν ∈ D.maximalSectors, D.weight ν

/-- Limiting mixture weight: normalized on maximal sectors and zero off them. -/
def pom_symmetric_group_gibbs_mixture_limitWeight
    (D : pom_symmetric_group_gibbs_mixture_data) (ν : Fin D.sectorCount) : ℝ :=
  if ν ∈ D.maximalSectors then
    D.weight ν / pom_symmetric_group_gibbs_mixture_maximalWeight D
  else
    0

/-- The limiting order parameter obtained by averaging a class observable over the maximal-layer
mixture. -/
def pom_symmetric_group_gibbs_mixture_limitOrderParameter
    (D : pom_symmetric_group_gibbs_mixture_data) : ℝ :=
  ∑ ν : Fin D.sectorCount,
    pom_symmetric_group_gibbs_mixture_limitWeight D ν * D.characterValue ν

/-- Paper-facing claim: nonmaximal normalized weights vanish, maximal weights converge to the
normalized positive mixture, and the maximal layer carries positive total mass. -/
def pom_symmetric_group_gibbs_mixture_claim
    (D : pom_symmetric_group_gibbs_mixture_data) : Prop :=
  (∀ ν : Fin D.sectorCount,
    Tendsto (fun m : ℕ => D.normalizedWeight m ν) atTop
      (nhds (pom_symmetric_group_gibbs_mixture_limitWeight D ν))) ∧
    0 < pom_symmetric_group_gibbs_mixture_maximalWeight D ∧
      pom_symmetric_group_gibbs_mixture_limitOrderParameter D =
        ∑ ν : Fin D.sectorCount,
          pom_symmetric_group_gibbs_mixture_limitWeight D ν * D.characterValue ν

/-- Paper label: `thm:pom-symmetric-group-gibbs-mixture`. Splitting finite sectors into maximal
and nonmaximal layers gives vanishing nonmaximal mass and the normalized Gibbs mixture on the
maximal layer. -/
theorem paper_pom_symmetric_group_gibbs_mixture
    (D : pom_symmetric_group_gibbs_mixture_data) :
    pom_symmetric_group_gibbs_mixture_claim D := by
  refine ⟨?_, ?_, rfl⟩
  · intro ν
    by_cases hν : ν ∈ D.maximalSectors
    · simpa [pom_symmetric_group_gibbs_mixture_limitWeight,
        pom_symmetric_group_gibbs_mixture_maximalWeight, hν] using
        D.maximal_converges ν hν
    · simpa [pom_symmetric_group_gibbs_mixture_limitWeight, hν] using
        D.nonmaximal_vanishes ν hν
  · exact Finset.sum_pos (fun ν hν => D.weight_pos ν hν) D.maximal_nonempty

end

end Omega.POM
