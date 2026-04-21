import Mathlib

namespace Omega.Conclusion

/-- The squarefree prime-shell code attached to a finite oriented-face pattern. -/
def squarefreePrimeShellCode (S : Finset ℕ) : ℕ :=
  S.prod id

/-- A finite oriented-face pattern lies in the boundary support exactly when every face in the
pattern occurs in that support. -/
def orientedBoundarySupportIncludes (S boundary : Finset ℕ) : Prop :=
  S ⊆ boundary

instance orientedBoundarySupportIncludesDecidable (S boundary : Finset ℕ) :
    Decidable (orientedBoundarySupportIncludes S boundary) :=
  inferInstanceAs (Decidable (S ⊆ boundary))

/-- Local squarefree Ramanujan coefficient on the Boolean divisor lattice. When the face-prime
already lies in the oriented boundary support, the local value is `p - 1`; otherwise it is `-1`.
-/
def booleanPrimeShellCoefficient (boundary T : Finset ℕ) : ℤ :=
  T.prod fun p => if p ∈ boundary then (p : ℤ) - 1 else -1

/-- The Boolean divisor-lattice sum over all subset-divisors of the prime-shell code. -/
def booleanDivisorTomographySum (S boundary : Finset ℕ) : ℤ :=
  (S.powerset).sum (booleanPrimeShellCoefficient boundary)

lemma booleanDivisorTomographySum_eq_localProduct (S boundary : Finset ℕ) :
    booleanDivisorTomographySum S boundary =
      S.prod (fun p => (if p ∈ boundary then (p : ℤ) - 1 else -1) + 1) := by
  unfold booleanDivisorTomographySum booleanPrimeShellCoefficient
  simpa using
    (Finset.prod_add_one (s := S)
      (f := fun p => if p ∈ boundary then (p : ℤ) - 1 else -1)).symm

/-- Paper label: `thm:conclusion-dyadic-boundary-primeshell-boolean-divisor-tomography`.
The Boolean-divisor-lattice Ramanujan telescope recovers the exact indicator that a finite
prime-shell pattern lies in the oriented boundary support. -/
theorem paper_conclusion_dyadic_boundary_primeshell_boolean_divisor_tomography
    (S boundary : Finset ℕ) :
    booleanDivisorTomographySum S boundary =
      if orientedBoundarySupportIncludes S boundary then (squarefreePrimeShellCode S : ℤ) else 0 := by
  classical
  rw [booleanDivisorTomographySum_eq_localProduct]
  have hsimp :
      S.prod (fun p => (if p ∈ boundary then (p : ℤ) - 1 else -1) + 1) =
        S.prod (fun p => if p ∈ boundary then (p : ℤ) else 0) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    by_cases hpB : p ∈ boundary <;> simp [hpB]
  rw [hsimp]
  by_cases h : orientedBoundarySupportIncludes S boundary
  · have hprod :
        S.prod (fun p => if p ∈ boundary then (p : ℤ) else 0) = S.prod (fun p => (p : ℤ)) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      simp [h hp]
    rw [if_pos h]
    simpa [squarefreePrimeShellCode] using hprod
  · have hp : ∃ p ∈ S, p ∉ boundary := by
      simpa [orientedBoundarySupportIncludes, Finset.subset_iff] using h
    rcases hp with ⟨p, hpS, hpB⟩
    have hzero :
        S.prod (fun x => if x ∈ boundary then (x : ℤ) else 0) = 0 := by
      exact Finset.prod_eq_zero_iff.mpr ⟨p, hpS, by simp [hpB]⟩
    rw [if_neg h]
    exact hzero

end Omega.Conclusion
