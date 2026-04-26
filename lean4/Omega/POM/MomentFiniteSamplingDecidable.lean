import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the finite `q`-moment sampling test.  The two moment sequences are
evaluated from their length-`2d` Hankel windows by the same realization functional. -/
structure pom_moment_finite_sampling_decidable_Data where
  offset : ℕ
  rank : ℕ
  leftMoment : ℕ → ℝ
  rightMoment : ℕ → ℝ
  realizeFromWindow : (Fin (2 * rank) → ℝ) → ℕ → ℝ
  left_realization :
    ∀ n, leftMoment n = realizeFromWindow (fun i => leftMoment (offset + i.1)) n
  right_realization :
    ∀ n, rightMoment n = realizeFromWindow (fun i => rightMoment (offset + i.1)) n

namespace pom_moment_finite_sampling_decidable_Data

/-- The Hankel normal form is represented by the finite window that generates the realization. -/
def leftHankelNormalForm (D : pom_moment_finite_sampling_decidable_Data) :
    Fin (2 * D.rank) → ℝ :=
  fun i => D.leftMoment (D.offset + i.1)

/-- The Hankel normal form for the second moment sequence. -/
def rightHankelNormalForm (D : pom_moment_finite_sampling_decidable_Data) :
    Fin (2 * D.rank) → ℝ :=
  fun i => D.rightMoment (D.offset + i.1)

/-- Agreement on the decisive length-`2d` sampling window. -/
def sameWindow (D : pom_moment_finite_sampling_decidable_Data) : Prop :=
  D.leftHankelNormalForm = D.rightHankelNormalForm

/-- The two constructions return the same Hankel normal form. -/
def sameHankelNormalForm (D : pom_moment_finite_sampling_decidable_Data) : Prop :=
  D.leftHankelNormalForm = D.rightHankelNormalForm

/-- Equality of the full moment sequences. -/
def allMomentsEqual (D : pom_moment_finite_sampling_decidable_Data) : Prop :=
  ∀ n, D.leftMoment n = D.rightMoment n

/-- Fingerprints read from the normal form: the finite window and the resulting realization. -/
def leftFingerprint (D : pom_moment_finite_sampling_decidable_Data) :=
  (D.leftHankelNormalForm, D.realizeFromWindow D.leftHankelNormalForm)

/-- Fingerprints read from the second normal form. -/
def rightFingerprint (D : pom_moment_finite_sampling_decidable_Data) :=
  (D.rightHankelNormalForm, D.realizeFromWindow D.rightHankelNormalForm)

/-- Equality of all fingerprints determined by the shared normal form. -/
def sameFingerprints (D : pom_moment_finite_sampling_decidable_Data) : Prop :=
  D.leftFingerprint = D.rightFingerprint

end pom_moment_finite_sampling_decidable_Data

open pom_moment_finite_sampling_decidable_Data

/-- Paper label: `prop:pom-moment-finite-sampling-decidable`.  A common length-`2d`
Hankel window gives the same normal form; because both sequences are realized from that
window by the same realization functional, all moments and all derived fingerprints agree. -/
theorem paper_pom_moment_finite_sampling_decidable
    (D : pom_moment_finite_sampling_decidable_Data) :
    D.sameWindow -> D.sameHankelNormalForm ∧ D.allMomentsEqual ∧ D.sameFingerprints := by
  intro hWindow
  refine ⟨hWindow, ?_, ?_⟩
  · intro n
    calc
      D.leftMoment n = D.realizeFromWindow D.leftHankelNormalForm n := by
        simpa [leftHankelNormalForm] using D.left_realization n
      _ = D.realizeFromWindow D.rightHankelNormalForm n := by rw [hWindow]
      _ = D.rightMoment n := by
        simpa [rightHankelNormalForm] using (D.right_realization n).symm
  · simpa [sameFingerprints, leftFingerprint, rightFingerprint] using congrArg
      (fun window => (window, D.realizeFromWindow window)) hWindow

end Omega.POM
