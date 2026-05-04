import Mathlib.Tactic

namespace Omega.Conclusion

/-- The first three spectral layers where the noncontractible maximum is allowed to occur. -/
def conclusion_fiber_topological_maximization_threelevel_tax_layers : Finset ℕ :=
  Finset.Icc 0 2

/-- A concrete finite toy rank profile for the three-layer closure. -/
def conclusion_fiber_topological_maximization_threelevel_tax_fiber_rank (layer : ℕ) : ℕ :=
  layer + 1

/-- Paper label: `cor:conclusion-fiber-topological-maximization-threelevel-tax`. -/
def conclusion_fiber_topological_maximization_threelevel_tax_statement : Prop :=
  (∀ layer : ℕ, layer ≤ 2 →
    layer ∈ conclusion_fiber_topological_maximization_threelevel_tax_layers) ∧
    (∀ layer : ℕ, layer ∈ conclusion_fiber_topological_maximization_threelevel_tax_layers →
      conclusion_fiber_topological_maximization_threelevel_tax_fiber_rank layer ≤
        conclusion_fiber_topological_maximization_threelevel_tax_fiber_rank 2) ∧
      conclusion_fiber_topological_maximization_threelevel_tax_fiber_rank 2 = 3

theorem paper_conclusion_fiber_topological_maximization_threelevel_tax :
    conclusion_fiber_topological_maximization_threelevel_tax_statement := by
  constructor
  · intro layer hle
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le layer, hle⟩
  constructor
  · intro layer hmem
    have hle : layer ≤ 2 := (Finset.mem_Icc.mp hmem).2
    simp [conclusion_fiber_topological_maximization_threelevel_tax_fiber_rank]
    omega
  · rfl

end Omega.Conclusion
