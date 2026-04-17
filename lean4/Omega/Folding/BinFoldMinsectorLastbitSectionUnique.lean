import Mathlib.Tactic
import Omega.Folding.StableSyntax

namespace Omega

/-- Canonical extension by the final block `01`. -/
def append01 (u : X n) : X (n + 2) :=
  X.appendTrue (X.appendFalse u) (by
    simp [X.appendFalse])

/-- Any section of double restriction whose image is forced into the last-bit-`1` layer must be the
canonical `u ↦ u01` section. -/
theorem paper_fold_bin_minsector_lastbit1_section_unique (n : Nat) (ι : X n → X (n + 2))
    (hsec : ∀ u, X.restrict (X.restrict (ι u)) = u)
    (hlast : ∀ u, (ι u).1 ⟨n + 1, by omega⟩ = true) :
    ι = append01 := by
  funext u
  have hLast : Omega.last (ι u).1 = true := by
    simpa [Omega.last] using hlast u
  have hRestrictLastFalse : Omega.last (X.restrict (ι u)).1 = false := by
    simpa [X.EndsInZero, Omega.last, Omega.get] using
      (X.restrict_endsInZero_of_last_true (ι u) hLast)
  have hRestrictEq : X.restrict (ι u) = X.appendFalse u := by
    have hReconstruct :
        X.appendFalse (X.restrict (X.restrict (ι u))) = X.restrict (ι u) :=
      X.appendFalse_reconstruct (X.restrict (ι u)) hRestrictLastFalse
    simp [hsec u] at hReconstruct
    exact hReconstruct.symm
  have hAppendTrueEq :
      X.appendTrue (X.restrict (ι u)) (X.restrict_endsInZero_of_last_true (ι u) hLast) =
        X.appendTrue (X.appendFalse u) (by
          simp [X.appendFalse]) := by
    apply Subtype.ext
    simp [X.appendTrue_val, X.appendFalse_val, hRestrictEq]
  calc
    ι u = X.appendTrue (X.restrict (ι u))
        (X.restrict_endsInZero_of_last_true (ι u) hLast) := by
          symm
          exact
            X.appendTrue_reconstruct (ι u) hLast (X.restrict_endsInZero_of_last_true (ι u) hLast)
    _ = X.appendTrue (X.appendFalse u) (by
          simp [X.appendFalse]) := hAppendTrueEq
    _ = append01 u := rfl

end Omega
