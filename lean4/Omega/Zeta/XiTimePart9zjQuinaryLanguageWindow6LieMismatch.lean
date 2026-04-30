namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zj-quinary-language-window6-lie-mismatch`. -/
theorem paper_xi_time_part9zj_quinary_language_window6_lie_mismatch
    (M : Nat) (alphabetThreshold lieDecomposition noSu5 : Prop)
    (hThreshold : alphabetThreshold -> 5 <= M)
    (hNoSu5 : lieDecomposition -> noSu5) :
    alphabetThreshold -> lieDecomposition -> 5 <= M ∧ noSu5 := by
  intro hAlphabetThreshold hLieDecomposition
  exact ⟨hThreshold hAlphabetThreshold, hNoSu5 hLieDecomposition⟩

end Omega.Zeta
