import Mathlib.Data.Real.Basic

/-- Paper label: `thm:xi-time-part9q-perfect-zk-no-disambiguation-gain`. -/
theorem paper_xi_time_part9q_perfect_zk_no_disambiguation_gain
    (timeWithTranscript entropyGivenY entropyGivenTranscript fiberIndexTerm alphabetLog : ℝ)
    (hAlphabet : alphabetLog ≠ 0) (hPerfectZK : entropyGivenTranscript = entropyGivenY)
    (hCoding : timeWithTranscript = entropyGivenTranscript / alphabetLog)
    (hFiber : entropyGivenY = fiberIndexTerm) :
    timeWithTranscript = entropyGivenY / alphabetLog ∧
      timeWithTranscript = fiberIndexTerm / alphabetLog := by
  by_cases hZero : alphabetLog = 0
  · exact False.elim (hAlphabet hZero)
  refine ⟨?_, ?_⟩
  · rw [hCoding, hPerfectZK]
  · rw [hCoding, hPerfectZK, hFiber]
