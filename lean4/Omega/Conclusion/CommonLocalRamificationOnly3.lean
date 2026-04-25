import Mathlib.Tactic
import Omega.Zeta.XiLeyangSplitPrimesQuadraticCharacterFilter

namespace Omega.Conclusion

open Finset

/-- The explicit decic discriminant support used in the common-local-ramification comparison. -/
def conclusion_common_local_ramification_only_3_decicPrimeSupport : Finset ℕ := {3}

/-- The decic support excludes `37`. -/
theorem conclusion_common_local_ramification_only_3_decic_excludes_37 :
    37 ∉ conclusion_common_local_ramification_only_3_decicPrimeSupport := by
  simp [conclusion_common_local_ramification_only_3_decicPrimeSupport]

/-- The common-local-ramification package: the Lee-Yang quadratic support is `{3,37}`, the decic
support excludes `37`, and their common odd ramification is therefore exactly `{3}`. -/
def conclusion_common_local_ramification_only_3_statement : Prop :=
  Omega.Zeta.xiLeyangQuadraticRamifiedPrimes = ({3, 37} : Finset ℕ) ∧
    conclusion_common_local_ramification_only_3_decicPrimeSupport ⊆
      Omega.Zeta.xiLeyangQuadraticRamifiedPrimes ∧
    37 ∉ conclusion_common_local_ramification_only_3_decicPrimeSupport ∧
    Omega.Zeta.xiLeyangQuadraticRamifiedPrimes ∩
        conclusion_common_local_ramification_only_3_decicPrimeSupport =
      ({3} : Finset ℕ)

/-- Paper label: `thm:conclusion-common-local-ramification-only-3`. -/
theorem paper_conclusion_common_local_ramification_only_3 :
    conclusion_common_local_ramification_only_3_statement := by
  refine ⟨by simp [Omega.Zeta.xiLeyangQuadraticRamifiedPrimes], ?_, ?_, ?_⟩
  · intro p hp
    simp [conclusion_common_local_ramification_only_3_decicPrimeSupport,
      Omega.Zeta.xiLeyangQuadraticRamifiedPrimes] at hp ⊢
    omega
  · exact conclusion_common_local_ramification_only_3_decic_excludes_37
  · ext p
    simp [conclusion_common_local_ramification_only_3_decicPrimeSupport,
      Omega.Zeta.xiLeyangQuadraticRamifiedPrimes]

end Omega.Conclusion
