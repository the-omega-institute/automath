import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fixed-resolution-no-thermal-singularity`. -/
theorem paper_conclusion_fixed_resolution_no_thermal_singularity (Z : ℝ -> ℝ)
    (terms : ℝ -> List ℝ) (hZ : forall beta, Z beta = (terms beta).sum)
    (hpos : forall beta t, t ∈ terms beta -> 0 < t)
    (hnonempty : forall beta, terms beta ≠ []) : forall beta, 0 < Z beta := by
  intro beta
  rw [hZ beta]
  have hsum_nonneg : forall l : List ℝ, (forall t, t ∈ l -> 0 < t) -> 0 ≤ l.sum := by
    intro l hl
    induction l with
    | nil =>
        simp
    | cons a as ih =>
        have ha : 0 ≤ a := le_of_lt (hl a (by simp))
        have has : 0 ≤ as.sum := ih (fun t ht => hl t (by simp [ht]))
        simpa using add_nonneg ha has
  cases hterms : terms beta with
  | nil =>
      exact (hnonempty beta hterms).elim
  | cons a as =>
      have ha : 0 < a := hpos beta a (by simp [hterms])
      have has : 0 ≤ as.sum :=
        hsum_nonneg as (fun t ht => hpos beta t (by simp [hterms, ht]))
      simpa [hterms] using add_pos_of_pos_of_nonneg ha has

end Omega.Conclusion
