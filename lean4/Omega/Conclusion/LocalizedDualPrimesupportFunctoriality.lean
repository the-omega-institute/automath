import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersCrossHomClassification

namespace Omega.Conclusion

open Omega.Zeta

/-- The surrogate for a continuous surjection `Σ_S ↠ Σ_T` in the finite localized-dual model:
the dual discrete map is a cross-hom with nonzero scalar. -/
def conclusion_localized_dual_primesupport_functoriality_surjectiveModel
    (S T : Omega.Zeta.FinitePrimeLocalization) : Prop :=
  ∃ φ : Omega.Zeta.LocalizedCrossHom T S,
    Omega.Zeta.localizedCrossHomScalar φ ≠ 0

/-- The unit scalar cross-hom realizing the functorial map when `T ⊆ S`. -/
def conclusion_localized_dual_primesupport_functoriality_unitHom
    {S T : Omega.Zeta.FinitePrimeLocalization} (hTS : T ⊆ S) :
    Omega.Zeta.LocalizedCrossHom T S where
  val :=
    { toFun := fun z => z
      map_zero' := by simp
      map_add' := by
        intro x y
        simp }
  property := by
    intro hMissing
    rcases hMissing with ⟨p, hpT, hpNotS⟩
    exact False.elim (hpNotS (hTS hpT))

/-- Paper label: `thm:conclusion-localized-dual-primesupport-functoriality`.
In the Pontryagin-dual surrogate already formalized in the zeta chapter, nonzero continuous
surjections are exactly the maps induced by prime-support inclusions; applying this both ways
gives the isomorphism criterion. -/
def conclusion_localized_dual_primesupport_functoriality_statement : Prop :=
  ∀ S T : Omega.Zeta.FinitePrimeLocalization,
    (conclusion_localized_dual_primesupport_functoriality_surjectiveModel S T ↔ T ⊆ S) ∧
      ((conclusion_localized_dual_primesupport_functoriality_surjectiveModel S T ∧
          conclusion_localized_dual_primesupport_functoriality_surjectiveModel T S) ↔
        S = T)

theorem paper_conclusion_localized_dual_primesupport_functoriality :
    conclusion_localized_dual_primesupport_functoriality_statement := by
  intro S T
  have hClass := Omega.Zeta.paper_xi_localized_integers_cross_hom_classification T S
  have hClass' := Omega.Zeta.paper_xi_localized_integers_cross_hom_classification S T
  have hSurjIff :
      conclusion_localized_dual_primesupport_functoriality_surjectiveModel S T ↔ T ⊆ S := by
    constructor
    · intro hSurj
      rcases hSurj with ⟨φ, hφ⟩
      by_contra hTS
      have hzero := hClass.2 hTS φ (1 : Omega.Zeta.LocalizedIntegerGroup T)
      exact hφ (by simpa [Omega.Zeta.localizedCrossHomScalar] using hzero)
    · intro hTS
      refine ⟨conclusion_localized_dual_primesupport_functoriality_unitHom hTS, ?_⟩
      simp [conclusion_localized_dual_primesupport_functoriality_unitHom,
        Omega.Zeta.localizedCrossHomScalar]
  have hSurjIff' :
      conclusion_localized_dual_primesupport_functoriality_surjectiveModel T S ↔ S ⊆ T := by
    constructor
    · intro hSurj
      rcases hSurj with ⟨φ, hφ⟩
      by_contra hST
      have hzero := hClass'.2 hST φ (1 : Omega.Zeta.LocalizedIntegerGroup S)
      exact hφ (by simpa [Omega.Zeta.localizedCrossHomScalar] using hzero)
    · intro hST
      refine ⟨conclusion_localized_dual_primesupport_functoriality_unitHom hST, ?_⟩
      simp [conclusion_localized_dual_primesupport_functoriality_unitHom,
        Omega.Zeta.localizedCrossHomScalar]
  refine ⟨hSurjIff, ?_⟩
  · constructor
    · intro hIso
      rcases hIso with ⟨hST, hTS⟩
      exact Finset.Subset.antisymm (hSurjIff'.1 hTS) (hSurjIff.1 hST)
    · intro hEq
      subst hEq
      have hSS :
          conclusion_localized_dual_primesupport_functoriality_surjectiveModel S S := by
        exact hSurjIff.2 Finset.Subset.rfl
      exact ⟨hSS, hSS⟩

end Omega.Conclusion
