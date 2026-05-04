import Mathlib.Tactic

namespace Omega.Conclusion

/-- Wulff-ray collision closure: the normalized ray collision product is locked at one. -/
def conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_rayCollision
    (F ColRay : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, F m * ColRay m = 1

/-- Golden-bulk divergence: the shifted bulk product eventually exceeds every threshold. -/
def conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_goldenBulkDivergence
    (F ColBulk : ℕ → ℝ) : Prop :=
  ∀ R : ℝ, ∃ m : ℕ, R ≤ F (m + 2) * ColBulk m

/-- A single Wulff scale source would identify the shifted bulk and ray products. -/
def conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_sameSource
    (F ColRay ColBulk : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, F (m + 2) * ColBulk m = F m * ColRay m

/-- Concrete paper-facing incompatibility statement. -/
def conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_statement : Prop :=
  ∀ F ColRay ColBulk : ℕ → ℝ,
    conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_rayCollision F ColRay →
      conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_goldenBulkDivergence
        F ColBulk →
        conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_sameSource
          F ColRay ColBulk →
          False

/-- Paper label: `cor:conclusion-serrin-wulff-ray-no-golden-bulk-resonance-source`. -/
theorem paper_conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source :
    conclusion_serrin_wulff_ray_no_golden_bulk_resonance_source_statement := by
  intro F ColRay ColBulk hRay hBulk hSame
  rcases hBulk 2 with ⟨m, hm⟩
  have hLocked : F (m + 2) * ColBulk m = 1 := by
    rw [hSame m, hRay m]
  linarith

end Omega.Conclusion
