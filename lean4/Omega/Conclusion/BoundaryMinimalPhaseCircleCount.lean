import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The explicit coordinate embedding of the phase grid
`Q_{p,ℓ}^{(r)} = (Fin (p^ℓ))^r` into `ℝ^r`, modeling the standard torus embedding used for the
sharpness direction of the theorem. -/
noncomputable def conclusion_boundary_minimal_phase_circle_count_coordinate_embedding
    (p ell r : ℕ) : (Fin r → Fin (p ^ ell)) → Fin r → ℝ :=
  fun a i => (a i : ℝ) / (p ^ ell : ℝ)

/-- Concrete data for the minimal phase-circle count argument. The packing estimate is recorded in
the sharp normalized form `δ_ℓ ≤ p^{-ℓ r / d}` and the native scale is the exact `p^{-ℓ}` depth.
-/
structure conclusion_boundary_minimal_phase_circle_count_data where
  p : ℕ
  ell : ℕ
  r : ℕ
  d : ℕ
  hp : 1 < p
  hell : 0 < ell
  hd : 0 < d
  delta : ℝ
  hdelta_pos : 0 < delta
  hpacking : delta ≤ (p : ℝ) ^ (-(((ell * r : ℕ) : ℝ) / d))

private lemma conclusion_boundary_minimal_phase_circle_count_native_forces_rank_bound
    (D : conclusion_boundary_minimal_phase_circle_count_data)
    (hnative : D.delta = (D.p : ℝ) ^ (-(D.ell : ℝ))) : D.r ≤ D.d := by
  have hp_real_gt_one : 1 < (D.p : ℝ) := by exact_mod_cast D.hp
  have hp_real_pos : 0 < (D.p : ℝ) := by linarith
  have hp_real_ne_one : (D.p : ℝ) ≠ 1 := ne_of_gt hp_real_gt_one
  have hlog_le :
      Real.logb D.p ((D.p : ℝ) ^ (-(D.ell : ℝ))) ≤
        Real.logb D.p ((D.p : ℝ) ^ (-(((D.ell * D.r : ℕ) : ℝ) / D.d))) := by
    rw [← hnative]
    exact Real.logb_le_logb_of_le hp_real_gt_one D.hdelta_pos D.hpacking
  have hleft :
      Real.logb D.p ((D.p : ℝ) ^ (-(D.ell : ℝ))) = -(D.ell : ℝ) := by
    rw [Real.logb_rpow hp_real_pos hp_real_ne_one]
  have hright :
      Real.logb D.p ((D.p : ℝ) ^ (-(((D.ell * D.r : ℕ) : ℝ) / D.d))) =
        -(((D.ell * D.r : ℕ) : ℝ) / D.d) := by
    rw [Real.logb_rpow hp_real_pos hp_real_ne_one]
  have hExp :
      -(D.ell : ℝ) ≤ -(((D.ell * D.r : ℕ) : ℝ) / D.d) := by
    linarith
  have hell_real_pos : 0 < (D.ell : ℝ) := by exact_mod_cast D.hell
  have hd_real_pos : 0 < (D.d : ℝ) := by exact_mod_cast D.hd
  have hdiv_le : (((D.ell * D.r : ℕ) : ℝ) / D.d) ≤ D.ell := by
    linarith
  have hmul : ((D.ell * D.r : ℕ) : ℝ) ≤ (D.ell : ℝ) * D.d := by
    exact (div_le_iff₀ hd_real_pos).mp hdiv_le
  have hmul' : (D.ell : ℝ) * D.r ≤ (D.ell : ℝ) * D.d := by
    simpa [Nat.cast_mul] using hmul
  have hr_le : (D.r : ℝ) ≤ D.d := by
    nlinarith
  exact_mod_cast hr_le

private lemma conclusion_boundary_minimal_phase_circle_count_coordinate_embedding_injective
    (p ell r : ℕ) (hp : 1 < p) :
    Function.Injective
      (conclusion_boundary_minimal_phase_circle_count_coordinate_embedding p ell r) := by
  intro a b hab
  funext i
  apply Fin.ext
  have hp_nat_pos : 0 < p := lt_trans Nat.zero_lt_one hp
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp_nat_pos
  have hden_ne : (p ^ ell : ℝ) ≠ 0 := by positivity
  have hcoord :
      ((a i : ℝ) / (p ^ ell : ℝ)) = ((b i : ℝ) / (p ^ ell : ℝ)) := by
    exact congrFun hab i
  have hval_real : (a i : ℝ) = (b i : ℝ) := by
    have hscaled := congrArg (fun x : ℝ => x * (p ^ ell : ℝ)) hcoord
    field_simp [hden_ne] at hscaled
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  exact_mod_cast hval_real

/-- Paper label: `thm:conclusion-boundary-minimal-phase-circle-count`. The normalized packing
bound forces the native phase scale `p^{-ℓ}` only when `d ≥ r`, and when `d = r` the standard
coordinate embedding of `(Fin (p^ℓ))^r` realizes the sharp phase-circle count. -/
theorem paper_conclusion_boundary_minimal_phase_circle_count
    (D : conclusion_boundary_minimal_phase_circle_count_data) :
    ((D.delta = (D.p : ℝ) ^ (-(D.ell : ℝ))) → D.r ≤ D.d) ∧
      (D.d = D.r →
        ∃ phi : (Fin D.r → Fin (D.p ^ D.ell)) → Fin D.r → ℝ, Function.Injective phi) := by
  refine ⟨conclusion_boundary_minimal_phase_circle_count_native_forces_rank_bound D, ?_⟩
  intro hdr
  refine ⟨conclusion_boundary_minimal_phase_circle_count_coordinate_embedding D.p D.ell D.r, ?_⟩
  exact conclusion_boundary_minimal_phase_circle_count_coordinate_embedding_injective
    D.p D.ell D.r D.hp

end Omega.Conclusion
