import Mathlib.Tactic

namespace Omega.SPG.CutFunctionSubmodular

open Finset

variable {V : Type*} [DecidableEq V]

/-- Cut indicator: 1 iff the endpoints lie on opposite sides of `S`.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
def cutIndicator (S : Finset V) (u v : V) : ℕ :=
  if (u ∈ S) ≠ (v ∈ S) then 1 else 0

/-- Pointwise submodular inequality for the cut indicator.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
theorem cutIndicator_submodular (S T : Finset V) (u v : V) :
    cutIndicator (S ∪ T) u v + cutIndicator (S ∩ T) u v ≤
      cutIndicator S u v + cutIndicator T u v := by
  unfold cutIndicator
  by_cases hu_S : u ∈ S <;> by_cases hu_T : u ∈ T <;>
    by_cases hv_S : v ∈ S <;> by_cases hv_T : v ∈ T <;>
    simp [Finset.mem_union, Finset.mem_inter, hu_S, hu_T, hv_S, hv_T]

/-- Cut weight over a finite edge set.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
def cutWeight {E : Type*} (edges : Finset E) (endpoints : E → V × V)
    (w : E → ℕ) (S : Finset V) : ℕ :=
  ∑ e ∈ edges, w e * cutIndicator S (endpoints e).1 (endpoints e).2

/-- Submodularity of the cut weight.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
theorem cutWeight_submodular {E : Type*} (edges : Finset E)
    (endpoints : E → V × V) (w : E → ℕ) (S T : Finset V) :
    cutWeight edges endpoints w (S ∪ T) + cutWeight edges endpoints w (S ∩ T) ≤
      cutWeight edges endpoints w S + cutWeight edges endpoints w T := by
  unfold cutWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h := cutIndicator_submodular S T (endpoints e).1 (endpoints e).2
  have hw : 0 ≤ w e := Nat.zero_le _
  nlinarith [h, hw]

/-- Paper package: strong subadditivity algebraic core for min-cut.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
theorem paper_spg_godel_rt_mincut_ssa_submodular
    {E : Type*} (edges : Finset E) (endpoints : E → V × V) (w : E → ℕ)
    (S T : Finset V) :
    cutWeight edges endpoints w (S ∪ T) + cutWeight edges endpoints w (S ∩ T) ≤
      cutWeight edges endpoints w S + cutWeight edges endpoints w T :=
  cutWeight_submodular edges endpoints w S T

/-- Paper-facing seeds wrapper for the min-cut SSA algebraic core.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
theorem paper_spg_godel_rt_mincut_uniqueness_ssa_seeds
    (edges : Finset (V × V)) (w : V × V → ℕ) (S T : Finset V) :
    cutWeight edges id w (S ∪ T) + cutWeight edges id w (S ∩ T) ≤
      cutWeight edges id w S + cutWeight edges id w T := by
  simpa using
    (paper_spg_godel_rt_mincut_ssa_submodular (V := V) edges id w S T)

/-- Package clone for the min-cut SSA algebraic core.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
theorem paper_spg_godel_rt_mincut_uniqueness_ssa_package
    (edges : Finset (V × V)) (w : V × V → ℕ) (S T : Finset V) :
    cutWeight edges id w (S ∪ T) + cutWeight edges id w (S ∩ T) ≤
      cutWeight edges id w S + cutWeight edges id w T :=
  paper_spg_godel_rt_mincut_uniqueness_ssa_seeds edges w S T

end Omega.SPG.CutFunctionSubmodular
