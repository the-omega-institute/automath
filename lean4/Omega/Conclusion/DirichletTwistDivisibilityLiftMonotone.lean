import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic
import Omega.Zeta.CyclotomicSectorIdentity

namespace Omega.Conclusion

open Omega.Zeta.CyclotomicSectorIdentity

noncomputable section

/-- Concrete divisibility-lift data for the Dirichlet-twist Fourier packet. The modulus `m` is at
least `2`, so there are nontrivial frequencies, and the lift factor `ell` is positive. -/
structure conclusion_dirichlet_twist_divisibility_lift_monotone_data where
  ell : ℕ
  m : ℕ
  hell : 1 ≤ ell
  hm : 2 ≤ m

/-- The base Dirichlet-twist matrix entry at a nontrivial frequency. -/
def conclusion_dirichlet_twist_divisibility_lift_monotone_base_matrix_entry
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (j : Fin (h.m - 1)) : ℂ :=
  rootOfUnity h.m (j.1 + 1)

/-- The lifted Dirichlet-twist matrix entry at a nontrivial frequency. -/
def conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_matrix_entry
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (k : Fin (h.ell * h.m - 1)) : ℂ :=
  rootOfUnity (h.ell * h.m) (k.1 + 1)

/-- The distinguished lifted frequency corresponding to the base frequency `j + 1`. -/
def conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (j : Fin (h.m - 1)) : Fin (h.ell * h.m - 1) := by
  refine ⟨h.ell * (j.1 + 1) - 1, ?_⟩
  have hell_pos : 0 < h.ell := Nat.succ_le_iff.mp h.hell
  have hm_pos : 0 < h.m := lt_of_lt_of_le (by decide : 0 < 2) h.hm
  have hj_lt : j.1 + 1 < h.m := by
    have hsucc : j.1 + 1 < (h.m - 1) + 1 := Nat.succ_lt_succ j.2
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)] using hsucc
  have hmul_lt : h.ell * (j.1 + 1) < h.ell * h.m :=
    Nat.mul_lt_mul_of_pos_left hj_lt hell_pos
  have hmul_pos : 0 < h.ell * (j.1 + 1) := Nat.mul_pos hell_pos (Nat.succ_pos _)
  omega

/-- The spectral weight attached to a base nontrivial frequency. -/
def conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_weight
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (j : Fin (h.m - 1)) : ℝ :=
  ‖1 - conclusion_dirichlet_twist_divisibility_lift_monotone_base_matrix_entry h j‖

/-- The spectral weight attached to a lifted nontrivial frequency. -/
def conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_weight
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (k : Fin (h.ell * h.m - 1)) : ℝ :=
  ‖1 - conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_matrix_entry h k‖

private lemma conclusion_dirichlet_twist_divisibility_lift_monotone_base_nonempty
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data) :
    (Finset.univ : Finset (Fin (h.m - 1))).Nonempty := by
  have hm1_pos : 0 < h.m - 1 := by
    apply Nat.sub_pos_of_lt
    exact lt_of_lt_of_le (by decide : 1 < 2) h.hm
  refine ⟨⟨0, hm1_pos⟩, by simp⟩

private lemma conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_nonempty
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data) :
    (Finset.univ : Finset (Fin (h.ell * h.m - 1))).Nonempty := by
  have hlift_ge_two : 2 ≤ h.ell * h.m := by
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ h.ell * h.m := Nat.mul_le_mul h.hell h.hm
  have hlift_pos : 0 < h.ell * h.m - 1 := by
    apply Nat.sub_pos_of_lt
    exact lt_of_lt_of_le (by decide : 1 < 2) hlift_ge_two
  refine ⟨⟨0, hlift_pos⟩, by simp⟩

/-- The base spectral radius is the maximum of the base spectral weights over the nontrivial
frequencies. -/
noncomputable def conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_radius
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data) : ℝ :=
  Finset.sup'
    (Finset.univ : Finset (Fin (h.m - 1)))
    (conclusion_dirichlet_twist_divisibility_lift_monotone_base_nonempty h)
    (conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_weight h)

/-- The lifted spectral radius is the maximum of the lifted spectral weights over the nontrivial
frequencies. -/
noncomputable def conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_radius
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data) : ℝ :=
  Finset.sup'
    (Finset.univ : Finset (Fin (h.ell * h.m - 1)))
    (conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_nonempty h)
    (conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_weight h)

private lemma conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index_succ
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (j : Fin (h.m - 1)) :
    (conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index h j).1 + 1 =
      h.ell * (j.1 + 1) := by
  unfold conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index
  have hell_pos : 0 < h.ell := Nat.succ_le_iff.mp h.hell
  have hprod_pos : 0 < h.ell * (j.1 + 1) := Nat.mul_pos hell_pos (Nat.succ_pos _)
  simp [Nat.sub_add_cancel (Nat.succ_le_of_lt hprod_pos)]

private theorem conclusion_dirichlet_twist_divisibility_lift_monotone_root_identity
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (j : Fin (h.m - 1)) :
    conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_matrix_entry h
        (conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index h j) =
      conclusion_dirichlet_twist_divisibility_lift_monotone_base_matrix_entry h j := by
  have hm0 : h.m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) h.hm)
  have hell0 : h.ell ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp h.hell)
  rw [conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_matrix_entry,
    conclusion_dirichlet_twist_divisibility_lift_monotone_base_matrix_entry,
    conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index_succ]
  unfold rootOfUnity
  congr 1
  field_simp [Nat.cast_mul, hm0, hell0]
  push_cast
  ring

private theorem conclusion_dirichlet_twist_divisibility_lift_monotone_weight_identity
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data)
    (j : Fin (h.m - 1)) :
    conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_weight h
        (conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index h j) =
      conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_weight h j := by
  rw [conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_weight,
    conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_weight,
    conclusion_dirichlet_twist_divisibility_lift_monotone_root_identity]

/-- The divisibility lift preserves the sampled root of unity on the distinguished frequencies,
preserves the corresponding spectral weights, and therefore cannot decrease the finite spectral
radius when one passes from modulus `m` to modulus `ell * m`. -/
def conclusion_dirichlet_twist_divisibility_lift_monotone_statement
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data) : Prop :=
  (∀ j : Fin (h.m - 1),
      conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_matrix_entry h
          (conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index h j) =
        conclusion_dirichlet_twist_divisibility_lift_monotone_base_matrix_entry h j) ∧
    (∀ j : Fin (h.m - 1),
      conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_weight h
          (conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index h j) =
        conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_weight h j) ∧
    conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_radius h ≤
      conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_radius h

/-- Paper label: `thm:conclusion-dirichlet-twist-divisibility-lift-monotone`. -/
theorem paper_conclusion_dirichlet_twist_divisibility_lift_monotone
    (h : conclusion_dirichlet_twist_divisibility_lift_monotone_data) :
    conclusion_dirichlet_twist_divisibility_lift_monotone_statement h := by
  refine ⟨conclusion_dirichlet_twist_divisibility_lift_monotone_root_identity h,
    conclusion_dirichlet_twist_divisibility_lift_monotone_weight_identity h, ?_⟩
  unfold conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_radius
  refine
    Finset.sup'_le
      (s := (Finset.univ : Finset (Fin (h.m - 1))))
      (f := conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_weight h)
      (H := conclusion_dirichlet_twist_divisibility_lift_monotone_base_nonempty h) ?_
  intro j hj
  calc
    conclusion_dirichlet_twist_divisibility_lift_monotone_base_spectral_weight h j =
        conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_weight h
          (conclusion_dirichlet_twist_divisibility_lift_monotone_lift_index h j) := by
            symm
            exact conclusion_dirichlet_twist_divisibility_lift_monotone_weight_identity h j
    _ ≤ conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_radius h := by
      unfold conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_radius
      exact
        Finset.le_sup'
          (s := (Finset.univ : Finset (Fin (h.ell * h.m - 1))))
          (f := conclusion_dirichlet_twist_divisibility_lift_monotone_lifted_spectral_weight h)
          (by simp)

end

end Omega.Conclusion
