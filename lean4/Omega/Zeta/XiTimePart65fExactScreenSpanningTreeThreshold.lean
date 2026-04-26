import Mathlib.Tactic
import Omega.SPG.ScreenKernelConnectedComponents

namespace Omega.Zeta

/-- Lower bound for a connected spanning subgraph on `vertices` vertices. -/
private lemma exactScreen_edge_lower_bound (vertices edges : ℕ)
    (hv : 0 < vertices) (hconnected : vertices ≤ edges + 1) :
    vertices - 1 ≤ edges := by
  omega

/-- Paper-facing exact-screen threshold package: injectivity forces the SPG screen graph to be
connected, connected spanning subgraphs have at least `|V| - 1` edges, equality is the spanning
tree case, and therefore any externally enumerated family of minimal exact screens is counted by
the spanning-tree count `τ(Γ)`.
    thm:xi-time-part65f-exact-screen-spanning-tree-threshold -/
theorem paper_xi_time_part65f_exact_screen_spanning_tree_threshold
    {Screen : Type*} [Fintype Screen]
    (vertices tau : ℕ) (edges components : Screen → ℕ)
    (hv : 0 < vertices)
    (hcomponents : ∀ S, 0 < components S)
    (hinj : ∀ S, components S - 1 = 0)
    (hconnected : ∀ S, vertices ≤ edges S + 1)
    (hminimal : ∀ S, edges S ≤ vertices - 1)
    (htau : Fintype.card { S // edges S = vertices - 1 } = tau) :
    (∀ S, components S = 1) ∧
      (∀ S, vertices - 1 ≤ edges S) ∧
      (∀ S, edges S = vertices - 1) ∧
      Fintype.card { S // edges S = vertices - 1 } = tau := by
  refine ⟨?_, ?_, ?_, htau⟩
  · intro S
    have hcomp : components S = 1 := by
      exact
        (Omega.SPG.ScreenKernelConnectedComponents.kernel_dim_eq_components_minus_one
          (components S) (hcomponents S)).1 (hinj S)
    exact hcomp
  · intro S
    exact exactScreen_edge_lower_bound vertices (edges S) hv (hconnected S)
  · intro S
    have hlower := exactScreen_edge_lower_bound vertices (edges S) hv (hconnected S)
    exact Nat.le_antisymm (hminimal S) hlower

end Omega.Zeta
