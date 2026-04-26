namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-continuous-base-universal-incomplete`. -/
theorem paper_conclusion_continuous_base_universal_incomplete
    (finitePrimeUniversal finitePrimeIncomplete leYangUniversal leYangIncomplete : Prop)
    (hFinite : finitePrimeUniversal ∧ finitePrimeIncomplete)
    (hLeeYang : leYangUniversal ∧ leYangIncomplete) :
    (finitePrimeUniversal ∧ leYangUniversal) ∧
      (finitePrimeIncomplete ∧ leYangIncomplete) := by
  exact ⟨⟨hFinite.1, hLeeYang.1⟩, ⟨hFinite.2, hLeeYang.2⟩⟩

end Omega.Conclusion
