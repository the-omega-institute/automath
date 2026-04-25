import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyP10HExplicitDensities
import Omega.Zeta.XiTimePart62ebLeyangExternalAuditImmunity

namespace Omega.Conclusion

/-- The `S₁₀` Frobenius factor. -/
abbrev conclusion_leyang_three_domain_frobenius_tensor_density_p10_group :=
  Equiv.Perm (Fin 10)

/-- The Lee--Yang cubic `S₃` Frobenius factor. -/
abbrev conclusion_leyang_three_domain_frobenius_tensor_density_leyang_group :=
  Equiv.Perm (Fin 3)

/-- The audited `L₄` factor modeled by `S₄ × C₂`. -/
abbrev conclusion_leyang_three_domain_frobenius_tensor_density_h_group :=
  Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2)

/-- The three-domain direct-product Galois model. -/
abbrev conclusion_leyang_three_domain_frobenius_tensor_density_joint_group :=
  conclusion_leyang_three_domain_frobenius_tensor_density_p10_group ×
    (conclusion_leyang_three_domain_frobenius_tensor_density_leyang_group ×
      conclusion_leyang_three_domain_frobenius_tensor_density_h_group)

/-- A finite subset is conjugacy-invariant when it is stable under inner automorphisms. -/
def conclusion_leyang_three_domain_frobenius_tensor_density_conjugacy_invariant
    {α : Type*} [Group α] (S : Finset α) : Prop :=
  ∀ σ τ : α, σ ∈ S → τ * σ * τ⁻¹ ∈ S

/-- The product density attached to three conjugacy-invariant subset factors. -/
noncomputable def conclusion_leyang_three_domain_frobenius_tensor_density_density
    (C : Finset conclusion_leyang_three_domain_frobenius_tensor_density_p10_group)
    (D : Finset conclusion_leyang_three_domain_frobenius_tensor_density_leyang_group)
    (E : Finset conclusion_leyang_three_domain_frobenius_tensor_density_h_group) : ℚ :=
  (C.card : ℚ) / Fintype.card conclusion_leyang_three_domain_frobenius_tensor_density_p10_group *
    ((D.card : ℚ) /
      Fintype.card conclusion_leyang_three_domain_frobenius_tensor_density_leyang_group) *
    ((E.card : ℚ) / Fintype.card conclusion_leyang_three_domain_frobenius_tensor_density_h_group)

/-- Paper label: `thm:conclusion-leyang-three-domain-frobenius-tensor-density`. The finite
direct-product model `S₁₀ × S₃ × (S₄ × C₂)` gives the exact product-cardinality density formula
for arbitrary conjugacy-invariant subset factors. The previously audited `P10`/Lee--Yang explicit
density package is recorded as the two special Lee--Yang split/irreducible instances. -/
theorem paper_conclusion_leyang_three_domain_frobenius_tensor_density :
    Nonempty
      (conclusion_leyang_three_domain_frobenius_tensor_density_joint_group ≃
        conclusion_leyang_three_domain_frobenius_tensor_density_p10_group ×
          conclusion_leyang_three_domain_frobenius_tensor_density_leyang_group ×
            conclusion_leyang_three_domain_frobenius_tensor_density_h_group) ∧
      Fintype.card conclusion_leyang_three_domain_frobenius_tensor_density_joint_group =
        Nat.factorial 10 * Nat.factorial 3 * 48 ∧
      (∀ C D E,
        conclusion_leyang_three_domain_frobenius_tensor_density_conjugacy_invariant C →
          conclusion_leyang_three_domain_frobenius_tensor_density_conjugacy_invariant D →
          conclusion_leyang_three_domain_frobenius_tensor_density_conjugacy_invariant E →
          conclusion_leyang_three_domain_frobenius_tensor_density_density C D E =
            (C.card : ℚ) / Nat.factorial 10 * ((D.card : ℚ) / 6) * ((E.card : ℚ) / 48)) ∧
      Omega.Folding.fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_irreducible_density =
        (1 : ℚ) / 20 ∧
      Omega.Folding.fold_gauge_anomaly_p10_leyang_irreducible_root_split_densities_split_density =
        (1 : ℚ) / 60 := by
  rcases Omega.Folding.paper_fold_gauge_anomaly_p10_h_explicit_densities with
    ⟨_, _, _, hirr, hsplit⟩
  refine ⟨⟨Equiv.refl _⟩, ?_, ?_, hirr, hsplit⟩
  · norm_num [conclusion_leyang_three_domain_frobenius_tensor_density_joint_group,
      Fintype.card_prod, Fintype.card_perm, Nat.factorial]
  · intro C D E _hC _hD _hE
    have hCardH :
        Fintype.card conclusion_leyang_three_domain_frobenius_tensor_density_h_group = 48 := by
      norm_num [conclusion_leyang_three_domain_frobenius_tensor_density_h_group, Fintype.card_prod,
        Fintype.card_perm]
    have hCardS3 :
        Fintype.card conclusion_leyang_three_domain_frobenius_tensor_density_leyang_group = 6 := by
      norm_num [conclusion_leyang_three_domain_frobenius_tensor_density_leyang_group,
        Fintype.card_perm]
    simp [conclusion_leyang_three_domain_frobenius_tensor_density_density, hCardH, hCardS3,
      Fintype.card_perm, mul_assoc]

end Omega.Conclusion
