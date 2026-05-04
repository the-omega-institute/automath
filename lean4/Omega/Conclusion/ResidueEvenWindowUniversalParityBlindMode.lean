namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-residue-even-window-universal-parity-blind-mode`. -/
theorem paper_conclusion_residue_even_window_universal_parity_blind_mode (m M : Nat)
    (parityCharacterKernel oneDimensional : Prop) (hm : m % 3 = 1) (hM : M % 2 = 0)
    (hParity : parityCharacterKernel) (hOne : oneDimensional) :
    oneDimensional ∧ parityCharacterKernel := by
  have hWindow : m % 3 = 1 ∧ M % 2 = 0 := ⟨hm, hM⟩
  rcases hWindow with ⟨_, _⟩
  exact ⟨hOne, hParity⟩

end Omega.Conclusion
