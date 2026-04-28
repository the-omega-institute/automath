import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-oddprime-affine-local-coarse-translation`. -/
theorem paper_conclusion_window6_oddprime_affine_local_coarse_translation
    (Paff Ploc Pcoarse : ℕ → Prop)
    (haff : ∀ p, Paff p ↔ p = 23)
    (hloc : ∀ p, Ploc p ↔ p = 3 ∨ p = 5 ∨ p = 23)
    (hcoarse : ∀ p, Pcoarse p ↔ p = 3 ∨ p = 571) :
    (∀ p, Paff p ↔ p = 23) ∧
      (∀ p, Ploc p ↔ p = 3 ∨ p = 5 ∨ p = 23) ∧
      (∀ p, Pcoarse p ↔ p = 3 ∨ p = 571) ∧
      (Paff 23 ∧ Ploc 23 ∧ ¬ Pcoarse 23) ∧
      (Pcoarse 571 ∧ ¬ Ploc 571) := by
  refine ⟨haff, hloc, hcoarse, ?_, ?_⟩
  · refine ⟨(haff 23).2 rfl, (hloc 23).2 (Or.inr (Or.inr rfl)), ?_⟩
    intro h23
    rcases (hcoarse 23).1 h23 with h3 | h571 <;> omega
  · refine ⟨(hcoarse 571).2 (Or.inr rfl), ?_⟩
    intro h571
    rcases (hloc 571).1 h571 with h3 | h5 | h23 <;> omega

end Omega.Conclusion
