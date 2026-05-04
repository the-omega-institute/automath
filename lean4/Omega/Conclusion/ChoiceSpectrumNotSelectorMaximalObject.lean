namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-choice-spectrum-not-selector-maximal-object`. -/
theorem paper_conclusion_choice_spectrum_not_selector_maximal_object
    (QuotientSpectrum SelectorObject MaximalStableObject : Prop)
    (hterm : QuotientSpectrum -> MaximalStableObject) (hnoSelector : SelectorObject -> False) :
    QuotientSpectrum -> MaximalStableObject /\ Not SelectorObject := by
  intro hQuotient
  exact ⟨hterm hQuotient, fun hSelector => hnoSelector hSelector⟩

end Omega.Conclusion
