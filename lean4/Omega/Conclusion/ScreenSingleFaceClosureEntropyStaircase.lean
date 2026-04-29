import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- Concrete screen-rank data for the single-face closure staircase. -/
structure conclusion_screen_single_face_closure_entropy_staircase_data where
  Point : Type*
  pointDecidableEq : DecidableEq Point
  rho : ℕ
  rank : Finset Point → ℕ
  rank_le_rho : ∀ S, rank S ≤ rho
  rank_mono : ∀ {S T}, S ⊆ T → rank S ≤ rank T
  rank_one_step : ∀ S e, rank (insert e S) ≤ rank S + 1
  rank_gain_when_deficient :
    ∀ S, 0 < rho - rank S → ∃ e : Point, rank (insert e S) = rank S + 1

namespace conclusion_screen_single_face_closure_entropy_staircase_data

instance (D : conclusion_screen_single_face_closure_entropy_staircase_data) :
    DecidableEq D.Point :=
  D.pointDecidableEq

/-- Audit deficit `a(S) = rho - r(S)`. -/
def conclusion_screen_single_face_closure_entropy_staircase_audit
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) (S : Finset D.Point) :
    ℕ :=
  D.rho - D.rank S

/-- Closure by the rank-gain zero characterization. -/
def conclusion_screen_single_face_closure_entropy_staircase_closure
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) (S : Finset D.Point) :
    Set D.Point :=
  {e | D.rank (insert e S) = D.rank S}

/-- A canonical deficient-rank extension, fixed by choice. -/
noncomputable def conclusion_screen_single_face_closure_entropy_staircase_stepSet
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) (S : Finset D.Point) :
    Finset D.Point :=
  if h : 0 < D.conclusion_screen_single_face_closure_entropy_staircase_audit S then
    insert (Classical.choose (D.rank_gain_when_deficient S h)) S
  else
    S

/-- One face changes the audit by either `0` or `1`, and closure is exactly zero gain. -/
def single_face_step (D : conclusion_screen_single_face_closure_entropy_staircase_data) : Prop :=
  ∀ S e,
    (D.conclusion_screen_single_face_closure_entropy_staircase_audit (insert e S) =
        D.conclusion_screen_single_face_closure_entropy_staircase_audit S ∨
      D.conclusion_screen_single_face_closure_entropy_staircase_audit (insert e S) + 1 =
        D.conclusion_screen_single_face_closure_entropy_staircase_audit S) ∧
      (e ∈ D.conclusion_screen_single_face_closure_entropy_staircase_closure S ↔
        D.conclusion_screen_single_face_closure_entropy_staircase_audit (insert e S) =
          D.conclusion_screen_single_face_closure_entropy_staircase_audit S)

/-- Deficient screens have an iterated strict descent to zero audit. -/
def strict_descent_chain_exists
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) : Prop :=
  ∀ S, ∃ chain : ℕ → Finset D.Point,
    chain 0 = S ∧
      (∀ i < D.conclusion_screen_single_face_closure_entropy_staircase_audit S,
        D.conclusion_screen_single_face_closure_entropy_staircase_audit (chain (i + 1)) <
          D.conclusion_screen_single_face_closure_entropy_staircase_audit (chain i)) ∧
        D.conclusion_screen_single_face_closure_entropy_staircase_audit
            (chain (D.conclusion_screen_single_face_closure_entropy_staircase_audit S)) = 0

private lemma conclusion_screen_single_face_closure_entropy_staircase_rank_gain_zero_or_one
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) (S : Finset D.Point)
    (e : D.Point) :
    D.rank (insert e S) = D.rank S ∨ D.rank (insert e S) = D.rank S + 1 := by
  have hmono : D.rank S ≤ D.rank (insert e S) := D.rank_mono (subset_insert e S)
  have hstep : D.rank (insert e S) ≤ D.rank S + 1 := D.rank_one_step S e
  omega

private lemma conclusion_screen_single_face_closure_entropy_staircase_audit_eq_iff
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) (S : Finset D.Point)
    (e : D.Point) :
    D.conclusion_screen_single_face_closure_entropy_staircase_audit (insert e S) =
        D.conclusion_screen_single_face_closure_entropy_staircase_audit S ↔
      D.rank (insert e S) = D.rank S := by
  have hS := D.rank_le_rho S
  have hSe := D.rank_le_rho (insert e S)
  constructor <;>
    intro h
  · dsimp [conclusion_screen_single_face_closure_entropy_staircase_audit] at h
    omega
  · dsimp [conclusion_screen_single_face_closure_entropy_staircase_audit]
    omega

private lemma conclusion_screen_single_face_closure_entropy_staircase_step_audit
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) (S : Finset D.Point) :
    D.conclusion_screen_single_face_closure_entropy_staircase_audit
        (D.conclusion_screen_single_face_closure_entropy_staircase_stepSet S) =
      D.conclusion_screen_single_face_closure_entropy_staircase_audit S - 1 := by
  classical
  by_cases h : 0 < D.conclusion_screen_single_face_closure_entropy_staircase_audit S
  · have hgain :=
      Classical.choose_spec (D.rank_gain_when_deficient S h)
    have hS := D.rank_le_rho S
    have hStep := D.rank_le_rho
      (insert (Classical.choose (D.rank_gain_when_deficient S h)) S)
    rw [conclusion_screen_single_face_closure_entropy_staircase_stepSet]
    simp only [dif_pos h]
    dsimp [conclusion_screen_single_face_closure_entropy_staircase_audit]
    rw [hgain]
    omega
  · simp [conclusion_screen_single_face_closure_entropy_staircase_stepSet, h]
    omega

private lemma conclusion_screen_single_face_closure_entropy_staircase_iterate_audit
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) (S : Finset D.Point) :
    ∀ i,
      D.conclusion_screen_single_face_closure_entropy_staircase_audit
          ((D.conclusion_screen_single_face_closure_entropy_staircase_stepSet)^[i] S) =
        D.conclusion_screen_single_face_closure_entropy_staircase_audit S - i := by
  intro i
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', conclusion_screen_single_face_closure_entropy_staircase_step_audit,
        ih]
      omega

/-- Paper label: `thm:conclusion-screen-single-face-closure-entropy-staircase`. -/
theorem paper_conclusion_screen_single_face_closure_entropy_staircase
    (D : conclusion_screen_single_face_closure_entropy_staircase_data) :
    D.single_face_step ∧ D.strict_descent_chain_exists := by
  classical
  refine ⟨?_, ?_⟩
  · intro S e
    constructor
    · rcases
        conclusion_screen_single_face_closure_entropy_staircase_rank_gain_zero_or_one D S e with
        hr | hr
      · left
        exact (conclusion_screen_single_face_closure_entropy_staircase_audit_eq_iff D S e).2 hr
      · right
        have hS := D.rank_le_rho S
        have hSe := D.rank_le_rho (insert e S)
        dsimp [conclusion_screen_single_face_closure_entropy_staircase_audit]
        omega
    · simpa [conclusion_screen_single_face_closure_entropy_staircase_closure] using
        (conclusion_screen_single_face_closure_entropy_staircase_audit_eq_iff D S e).symm
  · intro S
    refine ⟨fun i => (D.conclusion_screen_single_face_closure_entropy_staircase_stepSet)^[i] S,
      ?_, ?_, ?_⟩
    · simp
    · intro i hi
      rw [conclusion_screen_single_face_closure_entropy_staircase_iterate_audit,
        conclusion_screen_single_face_closure_entropy_staircase_iterate_audit]
      omega
    · rw [conclusion_screen_single_face_closure_entropy_staircase_iterate_audit]
      omega

end conclusion_screen_single_face_closure_entropy_staircase_data

end Omega.Conclusion
