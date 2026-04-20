import Mathlib.Tactic
import Omega.POM.FibCubeEdgeParity

namespace Omega.POM

open Omega.POM.FibCubeEdgeParity

/-- The exceptional component lengths whose Fibonacci fiber size is even, equivalently the
components lying in the residue class `1 mod 3`. -/
def toggleScanExceptionalLengths (lengths : List ℕ) : List ℕ :=
  lengths.filter fun ℓ => ℓ % 3 = 1

/-- Single-path scan sign, written in the `±1` convention of the paper. -/
def toggleScanSinglePathSign (ℓ : ℕ) : Int :=
  if fibConvSum ℓ % 2 = 0 then 1 else -1

/-- Product-fiber scan sign packaged exactly as the parity split from the paper: at least two
exceptional components force sign `+1`, a unique exceptional component contributes its own
single-path sign, and with no exceptional components every factor contributes. -/
def toggleScanGeneralFiberSign (lengths : List ℕ) : Int :=
  match toggleScanExceptionalLengths lengths with
  | _ :: _ :: _ => 1
  | [ℓ] => toggleScanSinglePathSign ℓ
  | [] =>
      if (lengths.map fun ℓ => fibConvSum ℓ % 2).sum % 2 = 0 then 1 else -1

/-- Paper-facing case split for the scan permutation on a product fiber.
    thm:pom-toggle-scan-sign-general-fiber -/
theorem paper_pom_toggle_scan_sign_general_fiber (lengths : List ℕ) :
    let A := toggleScanExceptionalLengths lengths
    (2 ≤ A.length → toggleScanGeneralFiberSign lengths = 1) ∧
      (∀ ℓ : ℕ, A = [ℓ] → toggleScanGeneralFiberSign lengths = toggleScanSinglePathSign ℓ) ∧
      (A = [] →
        toggleScanGeneralFiberSign lengths =
          if (lengths.map fun ℓ => fibConvSum ℓ % 2).sum % 2 = 0 then 1 else -1) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro hA
    unfold toggleScanGeneralFiberSign
    cases h : toggleScanExceptionalLengths lengths with
    | nil =>
        simp [h] at hA
    | cons a t =>
        cases t with
        | nil =>
            simp [h] at hA
        | cons b rest =>
            rfl
  · intro ℓ hA
    unfold toggleScanGeneralFiberSign
    rw [hA]
  · intro hA
    unfold toggleScanGeneralFiberSign
    rw [hA]

end Omega.POM
