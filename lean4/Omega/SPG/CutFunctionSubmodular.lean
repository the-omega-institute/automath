import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Prime
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

/-- The cut-edge support selected by `S` inside `edges`.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
def cutEdgeSupport (edges : Finset (V × V)) (S : Finset V) : Finset (V × V) :=
  edges.filter fun e => cutIndicator S e.1 e.2 = 1

/-- Prime-product encoding of the cut-edge support.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
def cutPrimeProduct (edges : Finset (V × V)) (q : V × V → ℕ) (S : Finset V) : ℕ :=
  ∏ e ∈ cutEdgeSupport edges S, q e

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

private theorem cutPrimeProduct_pos (edges : Finset (V × V)) (q : V × V → ℕ) (S : Finset V)
    (hq : ∀ e ∈ edges, 0 < q e) : 0 < cutPrimeProduct edges q S := by
  unfold cutPrimeProduct cutEdgeSupport
  refine Finset.prod_pos ?_
  intro e he
  exact hq e (Finset.mem_filter.mp he).1

private theorem cutPrimeProduct_log_le_iff (edges : Finset (V × V)) (q : V × V → ℕ)
    (S T : Finset V) (hq : ∀ e ∈ edges, 0 < q e) :
    (Real.log (cutPrimeProduct edges q S : ℝ) ≤ Real.log (cutPrimeProduct edges q T : ℝ)) ↔
      cutPrimeProduct edges q S ≤ cutPrimeProduct edges q T := by
  have hS_nat : 0 < cutPrimeProduct edges q S := cutPrimeProduct_pos edges q S hq
  have hT_nat : 0 < cutPrimeProduct edges q T := cutPrimeProduct_pos edges q T hq
  have hS : 0 < (cutPrimeProduct edges q S : ℝ) := by exact_mod_cast hS_nat
  have hT : 0 < (cutPrimeProduct edges q T : ℝ) := by exact_mod_cast hT_nat
  constructor
  · intro h
    exact_mod_cast (Real.log_le_log_iff hS hT).1 h
  · intro h
    exact (Real.log_le_log_iff hS hT).2 (by exact_mod_cast h)

private theorem cutEdgeSupport_eq_of_primeProduct_eq (edges : Finset (V × V)) (q : V × V → ℕ)
    (S T : Finset V) (hprime : ∀ e ∈ edges, Nat.Prime (q e))
    (hqinj : Set.InjOn q (↑edges : Set (V × V)))
    (hprod : cutPrimeProduct edges q S = cutPrimeProduct edges q T) :
    cutEdgeSupport edges S = cutEdgeSupport edges T := by
  apply Finset.Subset.antisymm
  · intro e heS
    have heEdge : e ∈ edges := (Finset.mem_filter.mp heS).1
    have hp : Nat.Prime (q e) := hprime e heEdge
    have hdivS : q e ∣ cutPrimeProduct edges q S := by
      unfold cutPrimeProduct
      exact Finset.dvd_prod_of_mem q heS
    have hdivT : q e ∣ cutPrimeProduct edges q T := by
      rw [← hprod]
      exact hdivS
    have hdivT' : q e ∣ ((cutEdgeSupport edges T).toList.map q).prod := by
      simpa [cutPrimeProduct] using hdivT
    have hprimeT : ∀ p ∈ (cutEdgeSupport edges T).toList.map q, Prime p := by
      intro p hpList
      rcases List.mem_map.mp hpList with ⟨f, hfList, rfl⟩
      exact Nat.prime_iff.mp (hprime f ((Finset.mem_filter.mp (Finset.mem_toList.mp hfList)).1))
    have hmemMap : q e ∈ (cutEdgeSupport edges T).toList.map q :=
      mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hp) hprimeT hdivT'
    rcases List.mem_map.mp hmemMap with ⟨f, hfList, hqf⟩
    have hfT : f ∈ cutEdgeSupport edges T := Finset.mem_toList.mp hfList
    have hfEdge : f ∈ edges := (Finset.mem_filter.mp hfT).1
    have hef : e = f := hqinj heEdge hfEdge hqf.symm
    simpa [hef] using hfT
  · intro e heT
    have heEdge : e ∈ edges := (Finset.mem_filter.mp heT).1
    have hp : Nat.Prime (q e) := hprime e heEdge
    have hdivT : q e ∣ cutPrimeProduct edges q T := by
      unfold cutPrimeProduct
      exact Finset.dvd_prod_of_mem q heT
    have hdivS : q e ∣ cutPrimeProduct edges q S := by
      rw [hprod]
      exact hdivT
    have hdivS' : q e ∣ ((cutEdgeSupport edges S).toList.map q).prod := by
      simpa [cutPrimeProduct] using hdivS
    have hprimeS : ∀ p ∈ (cutEdgeSupport edges S).toList.map q, Prime p := by
      intro p hpList
      rcases List.mem_map.mp hpList with ⟨f, hfList, rfl⟩
      exact Nat.prime_iff.mp (hprime f ((Finset.mem_filter.mp (Finset.mem_toList.mp hfList)).1))
    have hmemMap : q e ∈ (cutEdgeSupport edges S).toList.map q :=
      mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hp) hprimeS hdivS'
    rcases List.mem_map.mp hmemMap with ⟨f, hfList, hqf⟩
    have hfS : f ∈ cutEdgeSupport edges S := Finset.mem_toList.mp hfList
    have hfEdge : f ∈ edges := (Finset.mem_filter.mp hfS).1
    have hef : e = f := hqinj heEdge hfEdge hqf.symm
    simpa [hef] using hfS

/-- Paper-facing min-cut package: SSA for the cut weight, log/product monotonicity for positive
prime encodings, and uniqueness of the cut-edge support under an injective prime assignment.
    thm:spg-godel-rt-mincut-uniqueness-ssa -/
theorem paper_spg_godel_rt_mincut_uniqueness_ssa
    (edges : Finset (V × V)) (q : V × V → ℕ) :
    (∀ S T : Finset V,
      cutWeight edges id q (S ∪ T) + cutWeight edges id q (S ∩ T) ≤
        cutWeight edges id q S + cutWeight edges id q T) ∧
    (∀ S T : Finset V, (∀ e ∈ edges, 0 < q e) →
      ((Real.log (cutPrimeProduct edges q S : ℝ) ≤ Real.log (cutPrimeProduct edges q T : ℝ)) ↔
        cutPrimeProduct edges q S ≤ cutPrimeProduct edges q T)) ∧
    (∀ S T : Finset V, (∀ e ∈ edges, Nat.Prime (q e)) →
      Set.InjOn q (↑edges : Set (V × V)) →
      cutPrimeProduct edges q S = cutPrimeProduct edges q T →
      cutEdgeSupport edges S = cutEdgeSupport edges T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S T
    exact paper_spg_godel_rt_mincut_uniqueness_ssa_package edges q S T
  · intro S T
    intro hq
    exact cutPrimeProduct_log_le_iff edges q S T hq
  · intro S T hprime hqinj hprod
    exact cutEdgeSupport_eq_of_primeProduct_eq edges q S T hprime hqinj hprod

end Omega.SPG.CutFunctionSubmodular
