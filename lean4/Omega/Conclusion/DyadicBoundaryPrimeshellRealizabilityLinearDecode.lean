import Mathlib
import Omega.Conclusion.BoundaryGodelSyndromeCompletenessLinearDecode
import Omega.Conclusion.DyadicBoundaryPrimeshellBooleanDivisorTomography

namespace Omega.Conclusion

/-- The squarefree boundary code extracted from prime-shell data: the `p`-th coefficient is `1`
exactly on the observed shell support. -/
def conclusion_dyadic_boundary_primeshell_realizability_linear_decode_squarefree_boundary_code
    (shell : Finset ℕ) : ℕ → ℤ :=
  fun p => if p ∈ shell then 1 else 0

/-- Local syndrome closure for the extracted boundary code. -/
def conclusion_dyadic_boundary_primeshell_realizability_linear_decode_local_syndrome_closed
    {Syndrome : Type*}
    [Zero Syndrome]
    (syndrome : (ℕ → ℤ) → Syndrome) (b : ℕ → ℤ) : Prop :=
  syndrome b = 0

/-- Membership in the top-boundary image for the extracted code. -/
def conclusion_dyadic_boundary_primeshell_realizability_linear_decode_boundary_image
    {Cn : Type*}
    (boundaryTop : Cn → (ℕ → ℤ)) (b : ℕ → ℤ) : Prop :=
  ∃ x, boundaryTop x = b

/-- Paper label: `thm:conclusion-dyadic-boundary-primeshell-realizability-linear-decode`. The
Boolean divisor telescope identifies when the squarefree prime-shell data is exactly the oriented
boundary support, and the dyadic-boundary syndrome criterion upgrades the extracted code to
realizability, image membership, uniqueness, and linear-time bulk decoding. -/
theorem paper_conclusion_dyadic_boundary_primeshell_realizability_linear_decode
    {Cn Cn2 Syndrome : Type*}
    [AddGroup Cn] [AddGroup Cn2] [AddGroup Syndrome]
    (boundaryTop : Cn → (ℕ → ℤ))
    (boundaryLower : (ℕ → ℤ) → Cn2)
    (syndrome : (ℕ → ℤ) → Syndrome)
    (decodeFromBoundary : (ℕ → ℤ) → Cn)
    (work : (ℕ → ℤ) → Nat) (vertexCount edgeCount : Nat)
    (hSyndrome : ∀ b, syndrome b = 0 ↔ boundaryLower b = 0)
    (hChain : ∀ x, boundaryLower (boundaryTop x) = 0)
    (hExact : ∀ b, boundaryLower b = 0 → ∃ x, boundaryTop x = b)
    (hSub : ∀ u v, boundaryTop (u - v) = boundaryTop u - boundaryTop v)
    (hKer : ∀ u, boundaryTop u = 0 → u = 0)
    (hDecode : ∀ b, boundaryTop (decodeFromBoundary b) = b)
    (hLinear : ∀ b, work b ≤ vertexCount + edgeCount)
    (shell boundary : Finset ℕ)
    (hPrimePos : ∀ p ∈ shell, 0 < p) :
    (booleanDivisorTomographySum shell boundary = (squarefreePrimeShellCode shell : ℤ) ↔
      orientedBoundarySupportIncludes shell boundary) ∧
      let b :=
        conclusion_dyadic_boundary_primeshell_realizability_linear_decode_squarefree_boundary_code
          shell
      ((conclusion_dyadic_boundary_primeshell_realizability_linear_decode_boundary_image
            boundaryTop b ↔
          conclusion_dyadic_boundary_primeshell_realizability_linear_decode_local_syndrome_closed
            syndrome b) ∧
        (conclusion_dyadic_boundary_primeshell_realizability_linear_decode_local_syndrome_closed
              syndrome b ↔
            b ∈ Set.range boundaryTop) ∧
        (conclusion_dyadic_boundary_primeshell_realizability_linear_decode_local_syndrome_closed
              syndrome b →
            ∃! x, boundaryTop x = b ∧ work b ≤ vertexCount + edgeCount)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hsum
      by_cases hsupport : orientedBoundarySupportIncludes shell boundary
      · exact hsupport
      have hzero : booleanDivisorTomographySum shell boundary = 0 := by
        simpa [hsupport] using
          paper_conclusion_dyadic_boundary_primeshell_boolean_divisor_tomography shell boundary
      have hcode_pos : 0 < squarefreePrimeShellCode shell := by
        unfold squarefreePrimeShellCode
        exact Finset.prod_pos hPrimePos
      have hcode_ne : (squarefreePrimeShellCode shell : ℤ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hcode_pos
      have hcode_zero : (squarefreePrimeShellCode shell : ℤ) = 0 := hsum.symm.trans hzero
      exact False.elim (hcode_ne hcode_zero)
    · intro hsupport
      simpa [hsupport] using
        paper_conclusion_dyadic_boundary_primeshell_boolean_divisor_tomography shell boundary
  · dsimp
    have hmain :=
      paper_conclusion_boundary_godel_syndrome_completeness_linear_decode
        boundaryTop boundaryLower syndrome decodeFromBoundary work vertexCount edgeCount hSyndrome
        hChain hExact hSub hKer hDecode hLinear
        (conclusion_dyadic_boundary_primeshell_realizability_linear_decode_squarefree_boundary_code
          shell)
    refine ⟨?_, ?_, ?_⟩
    · simpa
        [conclusion_dyadic_boundary_primeshell_realizability_linear_decode_boundary_image,
          conclusion_dyadic_boundary_primeshell_realizability_linear_decode_local_syndrome_closed]
        using hmain.1
    · simpa
        [conclusion_dyadic_boundary_primeshell_realizability_linear_decode_local_syndrome_closed,
          Set.mem_range]
        using hmain.1.symm
    · simpa
        [conclusion_dyadic_boundary_primeshell_realizability_linear_decode_local_syndrome_closed]
        using hmain.2

end Omega.Conclusion
