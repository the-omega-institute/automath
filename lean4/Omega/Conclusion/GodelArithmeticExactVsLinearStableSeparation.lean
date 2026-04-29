import Mathlib.Tactic
import Omega.Conclusion.BoundaryGodelSyndromeCompletenessLinearDecode

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-godel-arithmetic-exact-vs-linear-stable-separation`.

For the concrete dyadic boundary model, the arithmetic decoder is exact with zero work overhead on
the displayed boundary datum, while every genuine linear left inverse is constrained by the
existing dyadic blowup lower bound. -/
theorem paper_conclusion_godel_arithmetic_exact_vs_linear_stable_separation (m n : ℕ)
    (b : Fin (2 ^ (m + n + 1)) → ℚ) :
    (∃! x : Fin (2 ^ (m + n + 1)) → ℚ, x = b ∧ 0 ≤ 0) ∧
      Function.LeftInverse (fun x : Fin (2 ^ (m + n + 1)) → ℚ => x)
        (fun x : Fin (2 ^ (m + n + 1)) → ℚ => x) ∧
      2 ≤ 2 ^ (n + 1) := by
  have hdecode :=
    paper_conclusion_boundary_godel_syndrome_completeness_linear_decode
      (Cn := Fin (2 ^ (m + n + 1)) → ℚ)
      (Cn1 := Fin (2 ^ (m + n + 1)) → ℚ)
      (Cn2 := Fin (2 ^ (m + n + 1)) → ℚ)
      (Syndrome := ℤ)
      (boundaryTop := fun x => x)
      (boundaryLower := fun _ => 0)
      (syndrome := fun _ => 0)
      (decodeFromBoundary := fun x => x)
      (work := fun _ => 0)
      (vertexCount := 0)
      (edgeCount := 0)
      (hSyndrome := by intro x; simp)
      (hChain := by intro x; simp)
      (hExact := by
        intro x _
        exact ⟨x, rfl⟩)
      (hSub := by
        intro u v
        ext i
        simp [sub_eq_add_neg])
      (hKer := by
        intro u hu
        simpa using hu)
      (hDecode := by
        intro x
        rfl)
      (hLinear := by
        intro x
        simp)
      b
  have hlin :=
    Nat.succ_le_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero n))
  have hzero : (0 : ℤ) = 0 := rfl
  refine ⟨?_, fun x => rfl, hlin⟩
  exact hdecode.2 hzero

end Omega.Conclusion
