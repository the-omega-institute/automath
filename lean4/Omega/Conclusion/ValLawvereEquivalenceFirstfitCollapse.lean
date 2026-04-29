import Mathlib.Logic.Nonempty

namespace Omega.Conclusion

universe u v

/-- Concrete data for the value-word quotient equivalence and the first-fit collapse obstruction.
The polynomial target supplies decidable Hom equality, while the first-fit relation is certified
undecidable. -/
structure conclusion_val_lawvere_equivalence_firstfit_collapse_data where
  conclusion_val_lawvere_equivalence_firstfit_collapse_word : Type u
  conclusion_val_lawvere_equivalence_firstfit_collapse_polyHom : Type v
  conclusion_val_lawvere_equivalence_firstfit_collapse_polyHom_decidableEq :
    DecidableEq conclusion_val_lawvere_equivalence_firstfit_collapse_polyHom
  conclusion_val_lawvere_equivalence_firstfit_collapse_valEq :
    conclusion_val_lawvere_equivalence_firstfit_collapse_word →
      conclusion_val_lawvere_equivalence_firstfit_collapse_word → Prop
  conclusion_val_lawvere_equivalence_firstfit_collapse_semantics :
    conclusion_val_lawvere_equivalence_firstfit_collapse_word →
      conclusion_val_lawvere_equivalence_firstfit_collapse_polyHom
  conclusion_val_lawvere_equivalence_firstfit_collapse_sound_complete :
    ∀ w1 w2,
      conclusion_val_lawvere_equivalence_firstfit_collapse_valEq w1 w2 ↔
        conclusion_val_lawvere_equivalence_firstfit_collapse_semantics w1 =
          conclusion_val_lawvere_equivalence_firstfit_collapse_semantics w2
  conclusion_val_lawvere_equivalence_firstfit_collapse_firstfitEq :
    conclusion_val_lawvere_equivalence_firstfit_collapse_word →
      conclusion_val_lawvere_equivalence_firstfit_collapse_word → Prop
  conclusion_val_lawvere_equivalence_firstfit_collapse_firstfit_undecidable :
    ¬ Nonempty
      (∀ w1 w2,
        Decidable
          (conclusion_val_lawvere_equivalence_firstfit_collapse_firstfitEq w1 w2))

namespace conclusion_val_lawvere_equivalence_firstfit_collapse_data

/-- Value-level soundness/completeness gives the Lawvere Hom-set bijection; any complete effective
translation of first-fit equality into decidable polynomial Hom equality would decide first-fit
extensional equality, contradicting the certificate. -/
def statement (D : conclusion_val_lawvere_equivalence_firstfit_collapse_data) : Prop :=
  (∀ w1 w2,
      D.conclusion_val_lawvere_equivalence_firstfit_collapse_valEq w1 w2 ↔
        D.conclusion_val_lawvere_equivalence_firstfit_collapse_semantics w1 =
          D.conclusion_val_lawvere_equivalence_firstfit_collapse_semantics w2) ∧
    ¬ ∃ translate :
        D.conclusion_val_lawvere_equivalence_firstfit_collapse_word →
          D.conclusion_val_lawvere_equivalence_firstfit_collapse_polyHom,
      ∀ w1 w2,
        D.conclusion_val_lawvere_equivalence_firstfit_collapse_firstfitEq w1 w2 ↔
          translate w1 = translate w2

end conclusion_val_lawvere_equivalence_firstfit_collapse_data

/-- Paper label: `thm:conclusion-val-lawvere-equivalence-firstfit-collapse`. -/
theorem paper_conclusion_val_lawvere_equivalence_firstfit_collapse
    (D : conclusion_val_lawvere_equivalence_firstfit_collapse_data) : D.statement := by
  refine ⟨D.conclusion_val_lawvere_equivalence_firstfit_collapse_sound_complete, ?_⟩
  rintro ⟨translate, hcomplete⟩
  letI :
      DecidableEq D.conclusion_val_lawvere_equivalence_firstfit_collapse_polyHom :=
    D.conclusion_val_lawvere_equivalence_firstfit_collapse_polyHom_decidableEq
  apply D.conclusion_val_lawvere_equivalence_firstfit_collapse_firstfit_undecidable
  refine ⟨fun w1 w2 => ?_⟩
  by_cases hEq : translate w1 = translate w2
  · exact isTrue ((hcomplete w1 w2).2 hEq)
  · exact isFalse (fun hFirstfit => hEq ((hcomplete w1 w2).1 hFirstfit))

end Omega.Conclusion
