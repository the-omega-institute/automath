import Mathlib.Tactic

namespace Omega.POM.HankelModMPurePeriodicity

/-- Pure periodicity of a finite group action along powers of a fixed element. -/
theorem paper_pom_hankel_modm_pure_periodicity {G H : Type*} [Group G] [Fintype G]
    [MulAction G H] (A : G) (H0 : H) :
    ∃ T : ℕ, 0 < T ∧ A ^ T = 1 ∧ ∀ r : ℕ, (A ^ (r + T)) • H0 = (A ^ r) • H0 := by
  refine ⟨orderOf A, orderOf_pos A, pow_orderOf_eq_one A, ?_⟩
  intro r
  simp [pow_add]

end Omega.POM.HankelModMPurePeriodicity
