import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.Conclusion

/-- The concrete finite `2`-torsion model used for the rank bound. -/
abbrev conclusion_serrin_wulff_localized_parity_rank_one_elementary_two_group (ν : ℕ) :=
  Fin ν → ZMod 2

/-- The `2`-torsion of a single circle factor, modeled by its sign coordinates. -/
abbrev conclusion_serrin_wulff_localized_parity_rank_one_torus_two_torsion :=
  Fin 1 → ZMod 2

/-- Faithful realization of an elementary `2`-group inside the `2`-torsion of a single circle. -/
def conclusion_serrin_wulff_localized_parity_rank_one_faithful_phase_model (ν : ℕ) : Prop :=
  ∃ ρ :
      conclusion_serrin_wulff_localized_parity_rank_one_elementary_two_group ν →+
        conclusion_serrin_wulff_localized_parity_rank_one_torus_two_torsion,
    Function.Injective ρ

private lemma conclusion_serrin_wulff_localized_parity_rank_one_rank_bound
    {ν : ℕ}
    (hρ : conclusion_serrin_wulff_localized_parity_rank_one_faithful_phase_model ν) :
    ν ≤ 1 := by
  rcases hρ with ⟨ρ, hρinj⟩
  have hcard :
      Fintype.card
          (conclusion_serrin_wulff_localized_parity_rank_one_elementary_two_group ν) ≤
        Fintype.card conclusion_serrin_wulff_localized_parity_rank_one_torus_two_torsion :=
    Fintype.card_le_of_injective ρ hρinj
  have hpows : 2 ^ ν ≤ 2 ^ 1 := by
    simpa [
      conclusion_serrin_wulff_localized_parity_rank_one_elementary_two_group,
      conclusion_serrin_wulff_localized_parity_rank_one_torus_two_torsion
    ] using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpows

/-- Paper label: `thm:conclusion-serrin-wulff-localized-parity-rank-one`.
This conclusion-level wrapper records the concrete product-of-`ℤ_p` model for the localized
Pontryagin-dual kernel and the resulting rank-one obstruction for any elementary `2`-group that
admits a faithful realization inside the `2`-torsion of a single circle factor. -/
def conclusion_serrin_wulff_localized_parity_rank_one_statement (S : Finset ℕ) : Prop :=
  Nonempty
      (Omega.CircleDimension.SolenoidProjectionKernel S ≃
        Omega.CircleDimension.SolenoidLocalizedQuotientDual S) ∧
    Nonempty
      (Omega.CircleDimension.SolenoidProjectionKernel S ≃
        Omega.CircleDimension.SolenoidKernelProductZpModel S) ∧
    ∀ ν : ℕ,
      conclusion_serrin_wulff_localized_parity_rank_one_faithful_phase_model ν →
        ν ≤ 1

theorem paper_conclusion_serrin_wulff_localized_parity_rank_one (S : Finset ℕ) :
    conclusion_serrin_wulff_localized_parity_rank_one_statement S := by
  refine ⟨(Omega.CircleDimension.paper_cdim_solenoid_kernel_product_zp S).1,
    (Omega.CircleDimension.paper_cdim_solenoid_kernel_product_zp S).2, ?_⟩
  intro ν hfaithful
  exact conclusion_serrin_wulff_localized_parity_rank_one_rank_bound hfaithful

end Omega.Conclusion
