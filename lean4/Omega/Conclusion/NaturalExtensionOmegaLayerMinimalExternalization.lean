import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-natural-extension-omega-layer-minimal-externalization`. -/
theorem paper_conclusion_natural_extension_omega_layer_minimal_externalization
    (minLayers : ℕ → ℕ) (naturalExtensionExact : Prop)
    (hmin : ∀ k, 1 ≤ k → minLayers k = k) (hnatural : naturalExtensionExact) :
    (∀ k, 1 ≤ k → minLayers k = k) ∧
      ¬ (∃ L, ∀ k, 1 ≤ k → minLayers k ≤ L) ∧ naturalExtensionExact := by
  refine ⟨hmin, ?_, hnatural⟩
  rintro ⟨L, hbounded⟩
  have hpos : 1 ≤ L + 1 := by omega
  have hle : minLayers (L + 1) ≤ L := hbounded (L + 1) hpos
  rw [hmin (L + 1) hpos] at hle
  omega

end Omega.Conclusion
