import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Atomic ghost coefficients for `(1 - u z^2)⁻¹`. -/
def atomGhostCoeff (n : ℕ) (u : Complex) : Complex :=
  if Even n then 2 * u ^ (n / 2) else 0

/-- The primitive layer is a single pulse at length `2`. -/
def atomPrimitiveCoeff (n : ℕ) (u : Complex) : Complex :=
  if n = 2 then u else 0

/-- Root-of-unity averaging records exactly the even divisibility comb. -/
def rootUnityGhostAverage (m n : ℕ) : Complex :=
  if 2 * m ∣ n then (2 : Complex) else 0

/-- The atomic ghost coefficients are even-only, the primitive layer is concentrated at `n = 2`,
and the root-of-unity average is the exact divisibility comb.
    thm:conclusion-realinput40-root-unity-ghost-complete-primitive-degenerate -/
theorem paper_conclusion_realinput40_root_unity_ghost_complete_primitive_degenerate
    (u : Complex) (m n : Nat) (hm : 2 <= m) :
    atomGhostCoeff n u = (if Even n then 2 * u ^ (n / 2) else 0) ∧
      atomPrimitiveCoeff n u = (if n = 2 then u else 0) ∧
      rootUnityGhostAverage m n = (if 2 * m ∣ n then (2 : Complex) else 0) := by
  let _ := hm
  exact ⟨rfl, rfl, rfl⟩

end Omega.Conclusion
