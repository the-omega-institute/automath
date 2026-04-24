import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit
import Omega.Zeta.XiCdimLocalizationQuotientSolenoidSurjections

namespace Omega.Zeta

/-- Torsion-freeness of the concrete discrete localization model `G_S = ℤ[S⁻¹] ⊆ ℚ`. -/
private lemma supportedLocalizedIntegerGroup_eq_zero_of_prime_zsmul_eq_zero
    {S : Finset Nat} {p : Nat} (hp : p.Prime) {x : SupportedLocalizedIntegerGroup S}
    (hx : (p : ℤ) • x = 0) : x = 0 := by
  have hxq : (p : ℚ) * (x : ℚ) = 0 := by
    have hx' := congrArg (fun q : SupportedLocalizedIntegerGroup S => (q : ℚ)) hx
    simpa [zsmul_eq_mul] using hx'
  have hx0 : (x : ℚ) = 0 := by
    exact (mul_eq_zero.mp hxq).resolve_left (by exact_mod_cast hp.ne_zero)
  ext
  simpa using hx0

/-- For every new prime in the quotient list `T \ S`, the dual localized extension cannot split as
`G_T ≃ G_S × ℤ/pℤ`: the quotient contributes a nonzero torsion summand, but `G_T` is torsion-free.
This is the discrete Pontryagin-dual obstruction behind the nonsplit circle extension.
    thm:xi-cdim-localization-solenoid-circle-extension-nonsplit -/
def XiCdimLocalizationSolenoidCircleExtensionNonsplit (S T : Finset Nat) : Prop :=
  ∀ ⦃p : Nat⦄, p.Prime → p ∈ xiLocalizationQuotientPrueferSummands S T →
    localizedIndex S p = p ∧
      localizedIndex T p = 1 ∧
      ¬ Nonempty (SupportedLocalizedIntegerGroup T ≃+ (SupportedLocalizedIntegerGroup S × ZMod p))

/-- Paper label: `thm:xi-cdim-localization-solenoid-circle-extension-nonsplit`. -/
theorem paper_xi_cdim_localization_solenoid_circle_extension_nonsplit
    (S T : Finset Nat) : XiCdimLocalizationSolenoidCircleExtensionNonsplit S T := by
  intro p hp hpList
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpDiff : p ∈ T \ S := by
    simpa [xiLocalizationQuotientPrueferSummands] using hpList
  have hpT : p ∈ T := (Finset.mem_sdiff.mp hpDiff).1
  have hpNotS : p ∉ S := (Finset.mem_sdiff.mp hpDiff).2
  refine ⟨(paper_xi_localized_quotient_index_prime_recovery S hp).2.1 hpNotS,
    (paper_xi_localized_quotient_index_prime_recovery T hp).1.1 hpT, ?_⟩
  rintro ⟨e⟩
  let x : SupportedLocalizedIntegerGroup T := e.symm (0, 1)
  have hx_ne : x ≠ 0 := by
    intro hx
    have hx_image : e x = 0 := by
      simpa [hx] using ((map_zero e).symm : e 0 = 0)
    have hpair : ((0 : SupportedLocalizedIntegerGroup S), (1 : ZMod p)) = 0 := by
      simpa [x] using hx_image
    have : (1 : ZMod p) = 0 := by
      simpa using congrArg Prod.snd hpair
    exact hp.ne_one (ZMod.one_eq_zero_iff.mp this)
  have hzmod : (p : ℤ) • (1 : ZMod p) = 0 := by
    rw [zsmul_eq_mul]
    simp
  have hpx : (p : ℤ) • x = 0 := by
    apply e.injective
    calc
      e ((p : ℤ) • x) = (p : ℤ) • e x := by
        simpa using (e.map_zsmul x (p : ℤ)).symm
      _ = (p : ℤ) • ((0 : SupportedLocalizedIntegerGroup S), (1 : ZMod p)) := by
        simp [x]
      _ = 0 := by
        ext <;> simp [hzmod]
      _ = e 0 := by
        simp
  exact hx_ne (supportedLocalizedIntegerGroup_eq_zero_of_prime_zsmul_eq_zero hp hpx)

end Omega.Zeta
