import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-large-prime-torsion-energy-eventual-monotone-from-below`. -/
theorem paper_conclusion_large_prime_torsion_energy_eventual_monotone_from_below
    (Prime : Nat → Prop) (E : Nat → ℝ) (P : ℝ)
    (hpos : ∃ p0, ∀ p, Prime p → p0 ≤ p → 0 < E p)
    (hbelow : ∃ p0, ∀ p, Prime p → p0 ≤ p → E p < P)
    (hmono : ∃ p0, ∀ p p', Prime p → Prime p' → p0 ≤ p → p < p' → E p < E p') :
    ∃ p0, ∀ p p', Prime p → Prime p' → p0 ≤ p → p < p' →
      0 < E p ∧ E p < E p' ∧ E p' < P := by
  rcases hpos with ⟨pPos, hPos⟩
  rcases hbelow with ⟨pBelow, hBelow⟩
  rcases hmono with ⟨pMono, hMono⟩
  refine ⟨max pPos (max pBelow pMono), ?_⟩
  intro p p' hp hp' hp0 hp_lt
  have hpos_le : pPos ≤ p := le_trans (Nat.le_max_left _ _) hp0
  have hbelow_le_p : pBelow ≤ p := by
    exact le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hp0
  have hbelow_le_p' : pBelow ≤ p' := le_trans hbelow_le_p (Nat.le_of_lt hp_lt)
  have hmono_le : pMono ≤ p := by
    exact le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hp0
  exact ⟨hPos p hp hpos_le, hMono p p' hp hp' hmono_le hp_lt,
    hBelow p' hp' hbelow_le_p'⟩

end Omega.Conclusion
