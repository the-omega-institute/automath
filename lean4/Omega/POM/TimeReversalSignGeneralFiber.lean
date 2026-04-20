import Omega.POM.ToggleOrder
import Omega.POM.ToggleScanSignGeneralFiber

namespace Omega.POM

open Omega.POM.ToggleOrder

/-- Single-path time-reversal sign in the paper's `±1` convention. -/
def toggleTimeReversalSinglePathSign (ℓ : ℕ) : Int :=
  if timeReversalSignExp ℓ % 2 = 0 then 1 else -1

/-- Product-fiber time-reversal sign packaged by the same exceptional-component split as the
paper statement: at least two `1 mod 3` components force sign `+1`, a unique exceptional
component contributes its own single-path sign, and otherwise every factor contributes. -/
def toggleTimeReversalGeneralFiberSign (lengths : List ℕ) : Int :=
  match toggleScanExceptionalLengths lengths with
  | _ :: _ :: _ => 1
  | [ℓ] => toggleTimeReversalSinglePathSign ℓ
  | [] => (lengths.map toggleTimeReversalSinglePathSign).prod

/-- Paper-facing case split for the time-reversal involution on a product fiber.
    thm:pom-toggle-time-reversal-sign-general-fiber -/
theorem paper_pom_toggle_time_reversal_sign_general_fiber (lengths : List ℕ) :
    let A := toggleScanExceptionalLengths lengths
    (2 ≤ A.length → toggleTimeReversalGeneralFiberSign lengths = 1) ∧
      (∀ ℓ : ℕ,
        A = [ℓ] →
          toggleTimeReversalGeneralFiberSign lengths = toggleTimeReversalSinglePathSign ℓ) ∧
      (A = [] →
        toggleTimeReversalGeneralFiberSign lengths =
          (lengths.map toggleTimeReversalSinglePathSign).prod) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro hA
    unfold toggleTimeReversalGeneralFiberSign
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
    unfold toggleTimeReversalGeneralFiberSign
    rw [hA]
  · intro hA
    unfold toggleTimeReversalGeneralFiberSign
    rw [hA]

end Omega.POM
