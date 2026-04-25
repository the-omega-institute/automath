import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence

namespace Omega.Zeta

open Omega.Conclusion

/-- Fixed finite-frequency certificates contribute at most `|S|` units to the natural collision
scale, so subtracting such a certificate from any already-divergent collision profile still
diverges. This is the abstract form of the finite-frequency obstruction used in the paper. -/
def xi_time_part9m_fixed_frequency_collision_certificate_fails_statement (S : Finset ℤ) : Prop :=
  ∀ M Col certificate : ℕ → ℝ,
    (∀ m, certificate m ≤ (S.card : ℝ)) →
      NatDivergesToInfinity (binfoldCollisionScaleTerm M Col) →
        NatDivergesToInfinity (fun m => binfoldCollisionScaleTerm M Col m - certificate m)

theorem xi_time_part9m_fixed_frequency_collision_certificate_fails_true (S : Finset ℤ) :
    xi_time_part9m_fixed_frequency_collision_certificate_fails_statement S := by
  intro M Col certificate hcertificate hdiv K
  obtain ⟨m, hm⟩ := hdiv (K + S.card)
  refine ⟨m, ?_⟩
  have hm' : (K : ℝ) + S.card ≤ binfoldCollisionScaleTerm M Col m := by
    simpa [Nat.cast_add] using hm
  have hcertm : certificate m ≤ (S.card : ℝ) := hcertificate m
  linarith

/-- Paper label: `thm:xi-time-part9m-fixed-frequency-collision-certificate-fails`. -/
def paper_xi_time_part9m_fixed_frequency_collision_certificate_fails (S : Finset ℤ) :
    Prop := by
  exact xi_time_part9m_fixed_frequency_collision_certificate_fails_statement S

end Omega.Zeta
