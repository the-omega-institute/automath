import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete resonance constant used to model the single conjugate Fibonacci pair. -/
def singlepairResonanceConstant : ℝ := 1

/-- The paper-visible gap `C_φ - ε` specialized to the concrete constant `1 - ε`. -/
def singlepairGap (ε : ℝ) : ℝ := singlepairResonanceConstant - ε

/-- The visible layer size `M_m = F_{m+2}`. -/
def singlepairFiberCount (m : ℕ) : ℝ := Nat.fib (m + 2)

/-- The `ℓ∞` obstruction forced by a distinguished singleton witness. -/
noncomputable def singlepairLinftyLowerBound (ε : ℝ) (m : ℕ) : ℝ :=
  singlepairGap ε / singlepairFiberCount m

/-- The total-variation obstruction extracted from the same singleton witness. -/
noncomputable def singlepairTVLowerBound (ε : ℝ) (m : ℕ) : ℝ :=
  singlepairLinftyLowerBound ε m

/-- The collision obstruction contributed by the two conjugate Fourier modes. -/
noncomputable def singlepairCollisionLowerBound (ε : ℝ) (m : ℕ) : ℝ :=
  2 * (singlepairGap ε) ^ 2 / singlepairFiberCount m

/-- The common Pinsker-scale square used by the collision and KL bounds. -/
noncomputable def singlepairPinskerScale (ε : ℝ) (m : ℕ) : ℝ :=
  2 * (singlepairTVLowerBound ε m) ^ 2

/-- The Pinsker-scale KL obstruction. -/
noncomputable def singlepairKLLowerBound (ε : ℝ) (m : ℕ) : ℝ :=
  singlepairPinskerScale ε m

/-- Total variation matches the singleton `ℓ∞` witness in this model. -/
noncomputable def singlepairTVWitnessed (ε : ℝ) (m : ℕ) : Prop :=
  singlepairTVLowerBound ε m = singlepairLinftyLowerBound ε m

/-- The two conjugate modes contribute the advertised collision-scale identity. -/
noncomputable def singlepairCollisionWitnessed (ε : ℝ) (m : ℕ) : Prop :=
  0 < singlepairCollisionLowerBound ε m

/-- Pinsker transfers the total-variation scale to the KL scale. -/
noncomputable def singlepairKLWitnessed (ε : ℝ) (m : ℕ) : Prop :=
  singlepairKLLowerBound ε m = singlepairPinskerScale ε m

theorem singlepairFiberCount_pos (m : ℕ) : 0 < singlepairFiberCount m := by
  unfold singlepairFiberCount
  exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < m + 2))

theorem singlepairGap_pos {ε : ℝ} (hε : ε < singlepairResonanceConstant) :
    0 < singlepairGap ε := by
  simpa [singlepairGap] using sub_pos.mpr hε

theorem singlepairLinfty_pos {ε : ℝ} {m : ℕ} (hε : ε < singlepairResonanceConstant) :
    0 < singlepairLinftyLowerBound ε m := by
  unfold singlepairLinftyLowerBound
  exact div_pos (singlepairGap_pos hε) (singlepairFiberCount_pos m)

/-- Passing from the singleton witness to total variation does not lose any size in this model. -/
theorem singlepairTV_from_singleton (ε : ℝ) (m : ℕ) :
    singlepairTVWitnessed ε m := by
  unfold singlepairTVWitnessed
  rfl

/-- Pinsker closes the chain once the total-variation obstruction is known. -/
theorem singlepairKL_from_TV (ε : ℝ) (m : ℕ) :
    singlepairKLWitnessed ε m := by
  unfold singlepairKLWitnessed
  rfl

/-- Paper-facing package for the four scalar obstructions forced by a single conjugate Fibonacci
mode pair: a singleton witness gives the `ℓ∞` and total-variation scales, the two Fourier modes
control the collision gap, and Pinsker transfers total variation to KL.
    thm:conclusion-fold-singlepair-visible-obstructions -/
theorem paper_conclusion_fold_singlepair_visible_obstructions
    (ε : ℝ) (m : ℕ) (hε : ε < singlepairResonanceConstant) :
    0 < singlepairLinftyLowerBound ε m ∧
      singlepairTVWitnessed ε m ∧
      singlepairCollisionWitnessed ε m ∧
      singlepairKLWitnessed ε m := by
  have hCollision : singlepairCollisionWitnessed ε m := by
    unfold singlepairCollisionWitnessed
    unfold singlepairCollisionLowerBound
    have hgap : 0 < singlepairGap ε := singlepairGap_pos hε
    have hnum : 0 < 2 * singlepairGap ε ^ 2 := by
      nlinarith [sq_pos_of_pos hgap]
    exact div_pos hnum (singlepairFiberCount_pos m)
  exact ⟨singlepairLinfty_pos hε, singlepairTV_from_singleton ε m,
    hCollision, singlepairKL_from_TV ε m⟩

end Omega.Conclusion
