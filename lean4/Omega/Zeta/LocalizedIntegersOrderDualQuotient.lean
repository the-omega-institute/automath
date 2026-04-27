import Omega.CircleDimension.SolenoidOverTMorphismClassification
import Omega.Zeta.LocalizedIntegersHomClassification

namespace Omega.Zeta

open Omega.CircleDimension

private lemma xi_localized_integers_order_dual_quotient_one_ne_zero (S : Finset Nat) :
    localizedOne S ≠ (0 : SupportedLocalizedIntegerGroup S) := by
  intro h
  have hq : ((localizedOne S : SupportedLocalizedIntegerGroup S) : ℚ) = 0 := by
    simpa using congrArg (fun x : SupportedLocalizedIntegerGroup S => (x : ℚ)) h
  norm_num [localizedOne] at hq

private lemma xi_localized_integers_order_dual_quotient_den_smul
    {S : Finset Nat} (x : SupportedLocalizedIntegerGroup S) :
    (x.1.den : ℤ) • x = x.1.num • localizedOne S := by
  ext
  have hden : (x.1.den : ℚ) ≠ 0 := by
    exact_mod_cast x.1.den_ne_zero
  have hrat : x.1 = (x.1.num : ℚ) / (x.1.den : ℚ) := (Rat.num_div_den x.1).symm
  change (x.1.den : ℚ) * x.1 = (x.1.num : ℚ) * (1 : ℚ)
  calc
    (x.1.den : ℚ) * x.1
        = (x.1.den : ℚ) * ((x.1.num : ℚ) / (x.1.den : ℚ)) := by
          congr 1
    _ = (x.1.den : ℚ) * ((x.1.num : ℚ) * (x.1.den : ℚ)⁻¹) := by
      rw [div_eq_mul_inv]
    _ = (x.1.num : ℚ) * ((x.1.den : ℚ) * (x.1.den : ℚ)⁻¹) := by ring
    _ = (x.1.num : ℚ) * 1 := by rw [mul_inv_cancel₀ hden]

private lemma xi_localized_integers_order_dual_quotient_hom_apply
    {S T : Finset Nat} (φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T)
    (x : SupportedLocalizedIntegerGroup S) :
    ((φ x : SupportedLocalizedIntegerGroup T) : ℚ) =
      ((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) * x.1 := by
  have hx := xi_localized_integers_order_dual_quotient_den_smul x
  have hmap :=
    congrArg (fun y : SupportedLocalizedIntegerGroup T => (y : ℚ)) (congrArg φ hx)
  have hden : (x.1.den : ℚ) ≠ 0 := by
    exact_mod_cast x.1.den_ne_zero
  have hrat : x.1 = (x.1.num : ℚ) / (x.1.den : ℚ) := (Rat.num_div_den x.1).symm
  have hφ :
      (x.1.den : ℚ) * ((φ x : SupportedLocalizedIntegerGroup T) : ℚ) =
        (x.1.num : ℚ) *
          ((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) := by
    simpa [map_zsmul, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hmap
  apply mul_left_cancel₀ hden
  calc
    (x.1.den : ℚ) * ((φ x : SupportedLocalizedIntegerGroup T) : ℚ)
        =
          (x.1.num : ℚ) *
            ((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) := hφ
    _ =
        (x.1.den : ℚ) *
          (((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) * x.1) := by
          calc
            (x.1.num : ℚ) *
                ((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ)
                =
                (x.1.den : ℚ) *
                  (((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) *
                    ((x.1.num : ℚ) * (x.1.den : ℚ)⁻¹)) := by
                rw [show
                    (x.1.den : ℚ) *
                        (((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) *
                          ((x.1.num : ℚ) * (x.1.den : ℚ)⁻¹)) =
                  ((x.1.num : ℚ) *
                      ((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ)) *
                    ((x.1.den : ℚ) * (x.1.den : ℚ)⁻¹) by ring]
                rw [mul_inv_cancel₀ hden, mul_one]
            _ =
                (x.1.den : ℚ) *
                  (((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) *
                    ((x.1.num : ℚ) / (x.1.den : ℚ))) := by
                rw [div_eq_mul_inv]
            _ =
                (x.1.den : ℚ) *
                  (((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ) * x.1) := by
                congr 1
                congr 1
                exact hrat.symm

private lemma xi_localized_integers_order_dual_quotient_subset_of_nonzero_hom
    {S T : Finset Nat} (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T)
    (hφ : φ (localizedOne S) ≠ 0) : S ⊆ T := by
  let D : LocalizedGsEmbeddingOrderData :=
    { S := S
      T := T
      S_primes := hS
      T_primes := hT }
  apply D.subset_of_localizedEmbedding
  refine ⟨((φ (localizedOne S) : SupportedLocalizedIntegerGroup T) : ℚ), ?_, ?_⟩
  · intro hzero
    apply hφ
    ext
    simpa using hzero
  · intro q hq
    let x : SupportedLocalizedIntegerGroup S := ⟨q, by
      intro p hp hdiv
      exact hq p hp hdiv⟩
    have hx := xi_localized_integers_order_dual_quotient_hom_apply φ x
    rw [← hx]
    exact (φ x).2

/-- Paper label: `cor:xi-localized-integers-order-dual-quotient`. -/
theorem paper_xi_localized_integers_order_dual_quotient
    (S T : Finset Nat) (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    (S ⊆ T ↔
        ∃ φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T,
          φ (localizedOne S) ≠ 0) ∧
      (S ⊆ T ↔
        ∃ φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T,
          Function.Injective φ) ∧
      (S ⊆ T ↔
        Omega.CircleDimension.LocalizedGsEmbeddingOrderData.compatibleDualSurjection S T) ∧
      (Nonempty (SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup T) ↔ S = T) := by
  let D : LocalizedGsEmbeddingOrderData :=
    { S := S
      T := T
      S_primes := hS
      T_primes := hT }
  have hHom := paper_xi_localized_integers_hom_classification S T
  have hOrder := Omega.CircleDimension.paper_cdim_solenoid_over_t_morphism_classification D
  have hNonzero :
      S ⊆ T ↔
        ∃ φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T,
          φ (localizedOne S) ≠ 0 := by
    constructor
    · intro hST
      obtain ⟨φ, hφ, _huniq⟩ := hHom.1 hST (localizedOne T)
      exact ⟨φ, by
        intro hzero
        exact xi_localized_integers_order_dual_quotient_one_ne_zero T (hφ.1.symm.trans hzero)⟩
    · rintro ⟨φ, hφ⟩
      exact xi_localized_integers_order_dual_quotient_subset_of_nonzero_hom hS hT φ hφ
  have hInjective :
      S ⊆ T ↔
        ∃ φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T,
          Function.Injective φ := by
    constructor
    · intro hST
      let φ := xi_localized_integers_hom_classification_scalarHom hST (localizedOne T)
      refine ⟨φ, ?_⟩
      intro x y hxy
      ext
      have hq := congrArg (fun z : SupportedLocalizedIntegerGroup T => (z : ℚ)) hxy
      simpa [φ, xi_localized_integers_hom_classification_scalarHom, localizedOne] using hq
    · rintro ⟨φ, hφinj⟩
      apply hNonzero.2
      refine ⟨φ, ?_⟩
      intro hzero
      have hone_zero : localizedOne S = (0 : SupportedLocalizedIntegerGroup S) := by
        apply hφinj
        simpa using hzero
      exact xi_localized_integers_order_dual_quotient_one_ne_zero S hone_zero
  refine ⟨hNonzero, hInjective, ?_, ?_⟩
  · exact hOrder.1.symm
  · constructor
    · rintro ⟨e⟩
      have hST : S ⊆ T := hInjective.2 ⟨e.toAddMonoidHom, e.injective⟩
      have hTS : T ⊆ S := by
        have hS' : ∀ p ∈ T, p.Prime := hT
        have hT' : ∀ p ∈ S, p.Prime := hS
        have hInjective' :
            T ⊆ S ↔
              ∃ φ : SupportedLocalizedIntegerGroup T →+ SupportedLocalizedIntegerGroup S,
                Function.Injective φ := by
          constructor
          · intro hTS
            let ψ := xi_localized_integers_hom_classification_scalarHom hTS (localizedOne S)
            refine ⟨ψ, ?_⟩
            intro x y hxy
            ext
            have hq := congrArg (fun z : SupportedLocalizedIntegerGroup S => (z : ℚ)) hxy
            simpa [ψ, xi_localized_integers_hom_classification_scalarHom, localizedOne] using hq
          · rintro ⟨ψ, hψinj⟩
            apply xi_localized_integers_order_dual_quotient_subset_of_nonzero_hom hS' hT' ψ
            intro hzero
            have hone_zero : localizedOne T = (0 : SupportedLocalizedIntegerGroup T) := by
              apply hψinj
              simpa using hzero
            exact xi_localized_integers_order_dual_quotient_one_ne_zero T hone_zero
        exact hInjective'.2 ⟨e.symm.toAddMonoidHom, e.symm.injective⟩
      exact Finset.Subset.antisymm hST hTS
    · intro hEq
      subst hEq
      exact ⟨AddEquiv.refl (SupportedLocalizedIntegerGroup S)⟩

end Omega.Zeta
