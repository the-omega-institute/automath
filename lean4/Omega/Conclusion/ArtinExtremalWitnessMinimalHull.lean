import Mathlib.Tactic

namespace Omega.Conclusion

/-- The equivalence relation identifying points that the witness cannot distinguish. -/
def conclusion_artin_extremal_witness_minimal_hull_setoid
    {G W : Type*} (ψ : G → W) : Setoid G where
  r x y := ψ x = ψ y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun hxy hyz => hxy.trans hyz⟩

/-- The minimal carrier quotient of a witness function. -/
abbrev conclusion_artin_extremal_witness_minimal_hull_quotient
    {G W : Type*} (ψ : G → W) :=
  Quotient (conclusion_artin_extremal_witness_minimal_hull_setoid ψ)

/-- The quotient projection onto the minimal carrier. -/
def conclusion_artin_extremal_witness_minimal_hull_projection
    {G W : Type*} (ψ : G → W) :
    G → conclusion_artin_extremal_witness_minimal_hull_quotient ψ :=
  Quotient.mk (conclusion_artin_extremal_witness_minimal_hull_setoid ψ)

/-- The witness pulled down to its minimal quotient. -/
def conclusion_artin_extremal_witness_minimal_hull_quotientWitness
    {G W : Type*} (ψ : G → W) :
    conclusion_artin_extremal_witness_minimal_hull_quotient ψ → W :=
  Quotient.lift ψ (by
    intro x y hxy
    exact hxy)

/-- The factor map from any quotient through which the witness factors to the minimal carrier. -/
noncomputable def conclusion_artin_extremal_witness_minimal_hull_descend
    {G H W : Type*} (ψ : G → W) (π : G → H) (hπ : Function.Surjective π)
    (_hfactor : ∀ x y : G, π x = π y → ψ x = ψ y) :
    H → conclusion_artin_extremal_witness_minimal_hull_quotient ψ := by
  classical
  intro h
  exact conclusion_artin_extremal_witness_minimal_hull_projection ψ (Classical.choose (hπ h))

lemma conclusion_artin_extremal_witness_minimal_hull_descend_comp
    {G H W : Type*} (ψ : G → W) (π : G → H) (hπ : Function.Surjective π)
    (hfactor : ∀ x y : G, π x = π y → ψ x = ψ y) (g : G) :
    conclusion_artin_extremal_witness_minimal_hull_descend ψ π hπ hfactor (π g) =
      conclusion_artin_extremal_witness_minimal_hull_projection ψ g := by
  classical
  unfold conclusion_artin_extremal_witness_minimal_hull_descend
  apply Quotient.sound
  exact hfactor (Classical.choose (hπ (π g))) g (Classical.choose_spec (hπ (π g)))

/-- Paper label: `thm:conclusion-artin-extremal-witness-minimal-hull`.
The quotient by equality of the extremal witness is the unique minimal carrier: the witness
factors uniquely through it, every threshold class union is pulled back from it, and every other
surjective carrier quotient through which the witness factors descends uniquely to it. -/
theorem paper_conclusion_artin_extremal_witness_minimal_hull
    {G H W Θ : Type*} (ψ : G → W) (π : G → H) (hπ : Function.Surjective π)
    (hfactor : ∀ x y : G, π x = π y → ψ x = ψ y) (threshold : Θ → W → Bool) :
    (∃! ψbar : conclusion_artin_extremal_witness_minimal_hull_quotient ψ → W,
        ∀ g : G, ψbar (conclusion_artin_extremal_witness_minimal_hull_projection ψ g) = ψ g) ∧
      (∀ θ : Θ, ∃ Abar : conclusion_artin_extremal_witness_minimal_hull_quotient ψ → Bool,
        ∀ g : G, threshold θ (ψ g) =
          Abar (conclusion_artin_extremal_witness_minimal_hull_projection ψ g)) ∧
      (∃! τ : H → conclusion_artin_extremal_witness_minimal_hull_quotient ψ,
        ∀ g : G, τ (π g) =
          conclusion_artin_extremal_witness_minimal_hull_projection ψ g) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨conclusion_artin_extremal_witness_minimal_hull_quotientWitness ψ, ?_, ?_⟩
    · intro g
      rfl
    · intro ψbar hψbar
      funext q
      refine Quotient.inductionOn q ?_
      intro g
      exact hψbar g
  · intro θ
    refine ⟨fun q =>
      threshold θ (conclusion_artin_extremal_witness_minimal_hull_quotientWitness ψ q), ?_⟩
    intro g
    rfl
  · refine ⟨conclusion_artin_extremal_witness_minimal_hull_descend ψ π hπ hfactor, ?_, ?_⟩
    · intro g
      exact conclusion_artin_extremal_witness_minimal_hull_descend_comp ψ π hπ hfactor g
    · intro τ hτ
      funext h
      rcases hπ h with ⟨g, rfl⟩
      exact (hτ g).trans
        (conclusion_artin_extremal_witness_minimal_hull_descend_comp ψ π hπ hfactor g).symm

end Omega.Conclusion
