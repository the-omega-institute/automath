import Mathlib.Tactic
import Omega.Zeta.XiTimePart50dcPeriodicResidueRationalCoreOctic
import Omega.Zeta.XiTimePart50dcAtomicPeriodicResidueCyclotomicShell

namespace Omega.Zeta

/-- Concrete coefficient and pole-order data for the full periodic-residue split. -/
structure xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data where
  m : ℕ
  r : ℕ
  hm : 2 ≤ m
  fullGeneratingFunctionCoefficients : ℕ → ℤ
  coreGeneratingFunctionCoefficients : ℕ → ℤ
  atomGeneratingFunctionCoefficients : ℕ → ℤ
  fullGeneratingFunctionCoefficients_split :
    ∀ n, fullGeneratingFunctionCoefficients n =
      coreGeneratingFunctionCoefficients n + atomGeneratingFunctionCoefficients n
  fullNonunitSingularityOrders : Finset ℕ
  coreNonunitSingularityOrders : Finset ℕ
  fullNonunitSingularityOrders_eq_core :
    fullNonunitSingularityOrders = coreNonunitSingularityOrders

namespace xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data

/-- The full generating function is represented coefficientwise as core plus atom. -/
def fullGeneratingFunctionSplit
    (D : xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data) : Prop :=
  ∀ n, D.fullGeneratingFunctionCoefficients n =
    D.coreGeneratingFunctionCoefficients n + D.atomGeneratingFunctionCoefficients n

/-- The atomic shell lies on the cyclotomic period `2m` and occupies one residue class. -/
def atomSingularitiesCyclotomic
    (D : xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data) : Prop :=
  let ell := if D.r % D.m = 0 then 2 * D.m else 2 * (D.r % D.m)
  0 < ell ∧ ell ≤ 2 * D.m ∧
    ∀ q : ℕ, 2 * ((if D.r % D.m = 0 then D.m else D.r % D.m) + q * D.m) =
      ell + q * (2 * D.m)

/-- Nonunit singularity orders of the full function are exactly the core orders. -/
def nonunitSingularitiesFromCore
    (D : xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data) : Prop :=
  ∀ n, n ∈ D.fullNonunitSingularityOrders ↔ n ∈ D.coreNonunitSingularityOrders

lemma fullGeneratingFunctionSplit_intro
    (D : xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data) :
    D.fullGeneratingFunctionSplit := by
  exact D.fullGeneratingFunctionCoefficients_split

lemma atomSingularitiesCyclotomic_intro
    (D : xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data) :
    D.atomSingularitiesCyclotomic := by
  exact paper_xi_time_part50dc_atomic_periodic_residue_cyclotomic_shell
    D.m D.r (lt_of_lt_of_le (by norm_num) D.hm)

lemma nonunitSingularitiesFromCore_intro
    (D : xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data) :
    D.nonunitSingularitiesFromCore := by
  intro n
  rw [D.fullNonunitSingularityOrders_eq_core]

end xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data

/-- Paper label:
`cor:xi-time-part50dc-full-periodic-residue-core-cyclotomic-splitting`. -/
theorem paper_xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting
    (D : xi_time_part50dc_full_periodic_residue_core_cyclotomic_splitting_Data) :
    D.fullGeneratingFunctionSplit ∧ D.atomSingularitiesCyclotomic ∧
      D.nonunitSingularitiesFromCore := by
  exact ⟨D.fullGeneratingFunctionSplit_intro, D.atomSingularitiesCyclotomic_intro,
    D.nonunitSingularitiesFromCore_intro⟩

end Omega.Zeta
