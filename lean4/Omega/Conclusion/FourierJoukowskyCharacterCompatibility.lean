import Omega.Conclusion.FourierJoukowskyWallcrossing

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-fourier-joukowsky-character-compatibility`. -/
theorem paper_conclusion_fourier_joukowsky_character_compatibility
    (characterAverageCompatibility characterJumpCompatibility componentwiseReconstruction : Prop)
    (h_average : characterAverageCompatibility)
    (h_jump : characterJumpCompatibility)
    (h_reconstruct :
      characterAverageCompatibility ∧ characterJumpCompatibility →
        componentwiseReconstruction) :
    characterAverageCompatibility ∧ characterJumpCompatibility ∧
      componentwiseReconstruction := by
  exact ⟨h_average, h_jump, h_reconstruct ⟨h_average, h_jump⟩⟩

end Omega.Conclusion
