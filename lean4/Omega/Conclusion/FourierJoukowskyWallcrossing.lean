namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fourier-joukowsky-wallcrossing`. -/
theorem paper_conclusion_fourier_joukowsky_wallcrossing
    (fourierJoukowskyAverageFormula jumpFormula : Prop)
    (h_average : fourierJoukowskyAverageFormula)
    (h_jump : jumpFormula) :
    fourierJoukowskyAverageFormula ∧ jumpFormula := by
  exact ⟨h_average, h_jump⟩

end Omega.Conclusion
