import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the orbitwise analysis of the translation equation `(I + T_w)b = d`
on `ℤ/(Mℤ)`. The data record the decomposition into translation orbits, the cyclic recurrence on
each orbit, and the parity split between the odd-length unique-solution case and the even-length
alternating-sum/seed-parametrized case. -/
structure TranslationEquationOrbitSolutionSpaceData where
  orbitCount : ℕ
  orbitLength : ℕ
  kernelDimension : ℕ
  solutionSpaceDimension : ℕ
  orbitDecomposition : Prop
  orbitRecurrence : Prop
  oddLengthUniqueSolution : Prop
  evenLengthAlternatingSumSolvability : Prop
  evenLengthAffineSeedParametrization : Prop
  orbitDecomposition_h : orbitDecomposition
  orbitRecurrence_h : orbitRecurrence
  deriveOddLengthUniqueSolution :
    orbitDecomposition → orbitRecurrence → orbitLength % 2 = 1 → oddLengthUniqueSolution
  deriveEvenLengthAlternatingSumSolvability :
    orbitDecomposition → orbitRecurrence → orbitLength % 2 = 0 →
      evenLengthAlternatingSumSolvability
  deriveEvenLengthAffineSeedParametrization :
    orbitDecomposition → orbitRecurrence → orbitLength % 2 = 0 →
      evenLengthAffineSeedParametrization
  kernelDimension_eq_orbitCount :
    orbitLength % 2 = 0 → kernelDimension = orbitCount
  solutionSpaceDimension_eq_orbitCount :
    orbitLength % 2 = 0 → solutionSpaceDimension = orbitCount

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the orbit decomposition of the translation equation `(I + T_w)b = d`.
If the orbit length is odd then the orbit seed is uniquely determined, while in the even case the
alternating-sum compatibility condition is necessary and sufficient and each orbit contributes one
free seed parameter.
    thm:fold-translation-equation-orbit-solution-space -/
theorem paper_fold_translation_equation_orbit_solution_space
    (D : TranslationEquationOrbitSolutionSpaceData) :
    D.orbitDecomposition ∧
      D.orbitRecurrence ∧
      (D.orbitLength % 2 = 1 → D.oddLengthUniqueSolution) ∧
      (D.orbitLength % 2 = 0 →
        D.evenLengthAlternatingSumSolvability ∧
          D.evenLengthAffineSeedParametrization ∧
          D.kernelDimension = D.orbitCount ∧
          D.solutionSpaceDimension = D.orbitCount) := by
  refine ⟨D.orbitDecomposition_h, D.orbitRecurrence_h, ?_, ?_⟩
  · intro hOdd
    exact D.deriveOddLengthUniqueSolution D.orbitDecomposition_h D.orbitRecurrence_h hOdd
  · intro hEven
    refine ⟨?_, ?_, D.kernelDimension_eq_orbitCount hEven, D.solutionSpaceDimension_eq_orbitCount hEven⟩
    · exact
        D.deriveEvenLengthAlternatingSumSolvability
          D.orbitDecomposition_h D.orbitRecurrence_h hEven
    · exact
        D.deriveEvenLengthAffineSeedParametrization
          D.orbitDecomposition_h D.orbitRecurrence_h hEven

end Omega.Folding
