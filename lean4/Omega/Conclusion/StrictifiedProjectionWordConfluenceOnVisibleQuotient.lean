namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-strictified-projection-word-confluence-on-visible-quotient`. -/
theorem paper_conclusion_strictified_projection_word_confluence_on_visible_quotient
    {Word : Type u} {VisibleLabel : Type v} {NormalForm : Type w}
    (reducesTo : Word → NormalForm → VisibleLabel → Prop)
    (h_exists : ∀ w, ∃ nf label, reducesTo w nf label)
    (h_confluent :
      ∀ {w nf1 nf2 label1 label2}, reducesTo w nf1 label1 → reducesTo w nf2 label2 →
        nf1 = nf2 ∧ label1 = label2) :
    (∀ w, ∃ nf label, reducesTo w nf label) ∧
      ∀ {w nf1 nf2 label1 label2}, reducesTo w nf1 label1 → reducesTo w nf2 label2 →
        nf1 = nf2 ∧ label1 = label2 := by
  exact ⟨h_exists, fun hleft hright => h_confluent hleft hright⟩

end Omega.Conclusion
