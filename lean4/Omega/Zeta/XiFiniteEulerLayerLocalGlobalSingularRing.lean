import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable def xi_finite_euler_layer_local_global_singular_ring_localDefect
    {V I : Type*} [Fintype I] (escape : V → I → Real) (v : V) : Real :=
  ∑ i, escape v i

noncomputable def xi_finite_euler_layer_local_global_singular_ring_globalDefect
    {V I : Type*} [Fintype V] [Fintype I] (escape : V → I → Real) : Real :=
  ∑ v, xi_finite_euler_layer_local_global_singular_ring_localDefect escape v

noncomputable def xi_finite_euler_layer_local_global_singular_ring_productLog
    {V I : Type*} [Fintype V] [Fintype I] (green : V → I → Real) : Real :=
  ∑ p : V × I, green p.1 p.2

/-- Paper label: `prop:xi-finite-euler-layer-local-global-singular-ring`.
Termwise singular-ring Green identities add over the finite Euler layer, and the product
polynomial logarithm is the finite sum of the logarithms of its trace-root factors. -/
theorem paper_xi_finite_euler_layer_local_global_singular_ring
    {V I : Type*} [Fintype V] [Fintype I]
    (escape green : V → I → Real) (hgreen : ∀ v i, escape v i = green v i) :
    xi_finite_euler_layer_local_global_singular_ring_globalDefect escape =
        ∑ v, ∑ i, green v i ∧
      xi_finite_euler_layer_local_global_singular_ring_productLog green =
        ∑ v, ∑ i, green v i ∧
      xi_finite_euler_layer_local_global_singular_ring_globalDefect escape =
        xi_finite_euler_layer_local_global_singular_ring_productLog green := by
  classical
  have hlocal :
      xi_finite_euler_layer_local_global_singular_ring_globalDefect escape =
        ∑ v, ∑ i, green v i := by
    unfold xi_finite_euler_layer_local_global_singular_ring_globalDefect
      xi_finite_euler_layer_local_global_singular_ring_localDefect
    refine Finset.sum_congr rfl ?_
    intro v hv
    exact Finset.sum_congr rfl (fun i hi => hgreen v i)
  have hproduct :
      xi_finite_euler_layer_local_global_singular_ring_productLog green =
        ∑ v, ∑ i, green v i := by
    unfold xi_finite_euler_layer_local_global_singular_ring_productLog
    rw [← Finset.univ_product_univ, Finset.sum_product]
  exact ⟨hlocal, hproduct, hlocal.trans hproduct.symm⟩

end Omega.Zeta
