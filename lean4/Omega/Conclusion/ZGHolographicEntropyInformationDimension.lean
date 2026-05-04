import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zg-holographic-pushforward-entropy-information-dimension`. -/
theorem paper_conclusion_zg_holographic_pushforward_entropy_information_dimension
    (blockEntropy primeScale : ℕ → ℝ) (infoDim : ℝ) (bounded : (ℕ → ℝ) → Prop)
    (hEntropy :
      bounded
        (fun n => blockEntropy n - (Real.log (primeScale n) + Real.log (Real.log (primeScale n)))))
    (hInfo :
      bounded
          (fun n =>
            blockEntropy n - (Real.log (primeScale n) + Real.log (Real.log (primeScale n)))) →
        infoDim = 0) :
    bounded
        (fun n =>
          blockEntropy n - (Real.log (primeScale n) + Real.log (Real.log (primeScale n)))) ∧
      infoDim = 0 := by
  exact ⟨hEntropy, hInfo hEntropy⟩

end Omega.Conclusion
