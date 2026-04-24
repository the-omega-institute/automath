import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable instance (G : Type*) [Group G] (Ω : Type*) [Fintype Ω] [MulAction G Ω] (ω : Ω) :
    Fintype ↥(MulAction.orbit G ω) := by
  classical
  infer_instance

noncomputable instance (G : Type*) [Fintype G] [Group G]
    (Ω : Type*) [MulAction G Ω] (ω : Ω) :
    Fintype ↥(MulAction.stabilizer G ω) := by
  classical
  infer_instance

theorem paper_xi_window6_group_quotient_isotropy_strata
    (G : Type*) [Group G] [Fintype G]
    (Ω : Type*) [Fintype Ω] [MulAction G Ω]
    (h2 : ∃ ω : Ω, Fintype.card ↥(MulAction.orbit G ω) = 2)
    (h3 : ∃ ω : Ω, Fintype.card ↥(MulAction.orbit G ω) = 3)
    (h4 : ∃ ω : Ω, Fintype.card ↥(MulAction.orbit G ω) = 4) :
    12 ∣ Fintype.card G := by
  rcases h2 with ⟨ω2, hω2⟩
  rcases h3 with ⟨ω3, hω3⟩
  rcases h4 with ⟨ω4, hω4⟩
  have h2dvd : 2 ∣ Fintype.card G := by
    refine ⟨Fintype.card (MulAction.stabilizer G ω2), ?_⟩
    simpa [hω2, mul_comm] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := G) (β := Ω) ω2).symm
  have h3dvd : 3 ∣ Fintype.card G := by
    refine ⟨Fintype.card (MulAction.stabilizer G ω3), ?_⟩
    simpa [hω3, mul_comm] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := G) (β := Ω) ω3).symm
  have h4dvd : 4 ∣ Fintype.card G := by
    refine ⟨Fintype.card (MulAction.stabilizer G ω4), ?_⟩
    simpa [hω4, mul_comm] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := G) (β := Ω) ω4).symm
  let _ := h2dvd
  simpa using
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 4 3) h4dvd h3dvd)

end Omega.Zeta
