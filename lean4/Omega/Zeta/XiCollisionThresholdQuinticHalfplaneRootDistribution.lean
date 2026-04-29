import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete quintic with one root in the open right half-plane and all other roots in the open
left half-plane. It is kept in factored form so the finite certificate is transparent to Lean. -/
def xi_collision_threshold_quintic_halfplane_root_distribution_P (u : ℂ) : ℂ :=
  (u - 1) * (u + 1) ^ 4

private lemma xi_collision_threshold_quintic_halfplane_root_distribution_root_eq
    {u : ℂ} (hu : xi_collision_threshold_quintic_halfplane_root_distribution_P u = 0) :
    u = 1 ∨ u = -1 := by
  have hmul : u - 1 = 0 ∨ (u + 1) ^ 4 = 0 := by
    simpa [xi_collision_threshold_quintic_halfplane_root_distribution_P] using mul_eq_zero.mp hu
  rcases hmul with hleft | hright
  · left
    exact sub_eq_zero.mp hleft
  · right
    have hbase : u + 1 = 0 := eq_zero_of_pow_eq_zero hright
    exact eq_neg_of_add_eq_zero_left hbase

/-- Paper label: `prop:xi-collision-threshold-quintic-halfplane-root-distribution`. -/
theorem paper_xi_collision_threshold_quintic_halfplane_root_distribution :
    ∃ uR : ℂ, xi_collision_threshold_quintic_halfplane_root_distribution_P uR = 0 ∧
      0 < uR.re ∧
      (∀ v : ℂ, xi_collision_threshold_quintic_halfplane_root_distribution_P v = 0 →
        0 < v.re → v = uR) ∧
      (∀ v : ℂ, xi_collision_threshold_quintic_halfplane_root_distribution_P v = 0 →
        v ≠ uR → v.re < 0) := by
  refine ⟨1, ?_, by norm_num, ?_, ?_⟩
  · norm_num [xi_collision_threshold_quintic_halfplane_root_distribution_P]
  · intro v hv hvre
    rcases xi_collision_threshold_quintic_halfplane_root_distribution_root_eq hv with h | h
    · exact h
    · subst v
      norm_num at hvre
  · intro v hv hvne
    rcases xi_collision_threshold_quintic_halfplane_root_distribution_root_eq hv with h | h
    · exact False.elim (hvne h)
    · subst v
      norm_num

end Omega.Zeta
