import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fiber-fixed-diameter-cube-chain-dual-extremals`. -/
theorem paper_conclusion_fiber_fixed_diameter_cube_chain_dual_extremals
    {Phase : Type}
    (volume symmetry : Phase → ℕ)
    (cube chain : Phase)
    (hVolMax : ∀ x, volume x ≤ volume cube)
    (hSymMax : ∀ x, symmetry x ≤ symmetry cube)
    (hVolMin : ∀ x, volume chain ≤ volume x)
    (hSymMin : ∀ x, symmetry chain ≤ symmetry x) :
    (∀ x, volume x ≤ volume cube ∧ symmetry x ≤ symmetry cube) ∧
      (∀ x, volume chain ≤ volume x ∧ symmetry chain ≤ symmetry x) := by
  exact ⟨fun x => ⟨hVolMax x, hSymMax x⟩, fun x => ⟨hVolMin x, hSymMin x⟩⟩

end Omega.Conclusion
