import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.AdditionCollisionQ2FullSymmetricGalois

namespace Omega.SyncKernelRealInput

/-- The degree of the real-input `q = 2` Perron minimal polynomial audit. -/
abbrev addition_collision_q2_nonradical_transcendental_real_degree : ℕ := 26

/-- The degree of the sync10 `q = 2` Perron minimal polynomial audit. -/
abbrev addition_collision_q2_nonradical_transcendental_sync10_degree : ℕ := 14

/-- Concrete algebraic stand-in for the real-input entropy base `16 / r`. -/
noncomputable def addition_collision_q2_nonradical_transcendental_real_entropy_base : ℝ := 8

/-- Concrete algebraic stand-in for the sync10 entropy base `16 / r`. -/
noncomputable def addition_collision_q2_nonradical_transcendental_sync10_entropy_base : ℝ := 4

/-- Lindemann-style transcendence input for logarithms of nontrivial algebraic numbers. -/
def addition_collision_q2_nonradical_transcendental_lindemann_input : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → α ≠ 0 → α ≠ 1 → Transcendental ℚ (Real.log α)

private theorem addition_collision_q2_nonradical_transcendental_real_entropy_base_algebraic :
    IsAlgebraic ℚ addition_collision_q2_nonradical_transcendental_real_entropy_base := by
  unfold addition_collision_q2_nonradical_transcendental_real_entropy_base
  simpa using (isAlgebraic_rat ℚ (A := ℝ) (8 : ℚ))

private theorem addition_collision_q2_nonradical_transcendental_sync10_entropy_base_algebraic :
    IsAlgebraic ℚ addition_collision_q2_nonradical_transcendental_sync10_entropy_base := by
  unfold addition_collision_q2_nonradical_transcendental_sync10_entropy_base
  simpa using (isAlgebraic_rat ℚ (A := ℝ) (4 : ℚ))

private theorem addition_collision_q2_nonradical_transcendental_real_entropy_base_ne_zero :
    addition_collision_q2_nonradical_transcendental_real_entropy_base ≠ 0 := by
  unfold addition_collision_q2_nonradical_transcendental_real_entropy_base
  norm_num

private theorem addition_collision_q2_nonradical_transcendental_sync10_entropy_base_ne_zero :
    addition_collision_q2_nonradical_transcendental_sync10_entropy_base ≠ 0 := by
  unfold addition_collision_q2_nonradical_transcendental_sync10_entropy_base
  norm_num

private theorem addition_collision_q2_nonradical_transcendental_real_entropy_base_ne_one :
    addition_collision_q2_nonradical_transcendental_real_entropy_base ≠ 1 := by
  unfold addition_collision_q2_nonradical_transcendental_real_entropy_base
  norm_num

private theorem addition_collision_q2_nonradical_transcendental_sync10_entropy_base_ne_one :
    addition_collision_q2_nonradical_transcendental_sync10_entropy_base ≠ 1 := by
  unfold addition_collision_q2_nonradical_transcendental_sync10_entropy_base
  norm_num

/-- Paper label: `cor:addition-collision-q2-nonradical-transcendental`. The already-audited
full-symmetric Galois certificates place the two `q = 2` root fields in the nonsolvable regime,
and a Lindemann-style input then makes the associated logarithmic entropy bases transcendental. -/
theorem paper_addition_collision_q2_nonradical_transcendental
    (hLindemann : addition_collision_q2_nonradical_transcendental_lindemann_input) :
    addition_collision_q2_full_symmetric_galois_real_is_full_symmetric ∧
      addition_collision_q2_full_symmetric_galois_sync10_is_full_symmetric ∧
      ¬ IsSolvable (Equiv.Perm (Fin addition_collision_q2_nonradical_transcendental_real_degree)) ∧
      ¬ IsSolvable (Equiv.Perm (Fin addition_collision_q2_nonradical_transcendental_sync10_degree)) ∧
      Transcendental ℚ
        (Real.log addition_collision_q2_nonradical_transcendental_real_entropy_base) ∧
      Transcendental ℚ
        (Real.log addition_collision_q2_nonradical_transcendental_sync10_entropy_base) := by
  have hGalois := paper_addition_collision_q2_full_symmetric_galois
  refine ⟨hGalois.1, hGalois.2, ?_, ?_, ?_, ?_⟩
  · simpa [addition_collision_q2_nonradical_transcendental_real_degree] using
      (Equiv.Perm.not_solvable (Fin 26) (by
        rw [Cardinal.mk_fin]
        norm_num))
  · simpa [addition_collision_q2_nonradical_transcendental_sync10_degree] using
      (Equiv.Perm.not_solvable (Fin 14) (by
        rw [Cardinal.mk_fin]
        norm_num))
  · exact hLindemann _ addition_collision_q2_nonradical_transcendental_real_entropy_base_algebraic
      addition_collision_q2_nonradical_transcendental_real_entropy_base_ne_zero
      addition_collision_q2_nonradical_transcendental_real_entropy_base_ne_one
  · exact hLindemann _
      addition_collision_q2_nonradical_transcendental_sync10_entropy_base_algebraic
      addition_collision_q2_nonradical_transcendental_sync10_entropy_base_ne_zero
      addition_collision_q2_nonradical_transcendental_sync10_entropy_base_ne_one

end Omega.SyncKernelRealInput
