import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.HydrogenicResidualAuditCapacity

namespace Omega.Conclusion

/-- Phase-blind hydrogenic classes indexed by an angular shell and `|m|`. -/
def conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_class (n : ℕ) : Type :=
  Σ l : Fin n, Fin (l.val + 1)

/-- Hydrogenic address fibers after the phase-blind projection. -/
abbrev conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_fiber
    (n : ℕ) (l : Fin n) (mu : Fin (l.val + 1)) : Type :=
  Fin (if (mu : ℕ) = 0 then 2 else 4)

/-- Full finite address model for the strict two-level gauge tower. -/
def conclusion_hydrogenic_strict_twolevel_gauge_tower_address (n : ℕ) : Type :=
  Σ l : Fin n, Σ mu : Fin (l.val + 1),
    conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_fiber n l mu

/-- The phase-blind projection records `(l, |m|)`. -/
def conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_projection {n : ℕ}
    (a : conclusion_hydrogenic_strict_twolevel_gauge_tower_address n) :
    conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_class n :=
  ⟨a.1, a.2.1⟩

/-- The class-function projection records only `l`. -/
def conclusion_hydrogenic_strict_twolevel_gauge_tower_classfunction_projection {n : ℕ}
    (a : conclusion_hydrogenic_strict_twolevel_gauge_tower_address n) : Fin n :=
  a.1

/-- The finite projection that forgets `|m|` from a phase-blind class. -/
def conclusion_hydrogenic_strict_twolevel_gauge_tower_finite_projection {n : ℕ}
    (p : conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_class n) : Fin n :=
  p.1

/-- Concrete finite statement for the strict two-level hydrogenic gauge tower. -/
def conclusion_hydrogenic_strict_twolevel_gauge_tower_statement (n : ℕ) : Prop :=
  (∀ a : conclusion_hydrogenic_strict_twolevel_gauge_tower_address n,
      conclusion_hydrogenic_strict_twolevel_gauge_tower_classfunction_projection a =
        conclusion_hydrogenic_strict_twolevel_gauge_tower_finite_projection
          (conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_projection a)) ∧
    (∀ (a : conclusion_hydrogenic_strict_twolevel_gauge_tower_address n) (l : Fin n),
      conclusion_hydrogenic_strict_twolevel_gauge_tower_classfunction_projection a = l ↔
        ∃ mu : Fin (l.val + 1),
          conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_projection a =
            ⟨l, mu⟩) ∧
    (∀ (l : Fin n) (mu₁ mu₂ : Fin (l.val + 1)),
      mu₁ ≠ mu₂ →
        ∀ a : conclusion_hydrogenic_strict_twolevel_gauge_tower_address n,
          conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_projection a =
              ⟨l, mu₁⟩ →
            conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_projection a =
              ⟨l, mu₂⟩ →
            False) ∧
    (∀ l : Fin n,
      Fintype.card
          (conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_fiber n l
            ⟨0, Nat.succ_pos l.val⟩) = 2) ∧
    ∀ (l : Fin n) (mu : Fin (l.val + 1)),
      0 < (mu : ℕ) →
        Fintype.card
            (conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_fiber n l mu) = 4

/-- Paper label: `thm:conclusion-hydrogenic-strict-twolevel-gauge-tower`. -/
theorem paper_conclusion_hydrogenic_strict_twolevel_gauge_tower
    (n : ℕ) (_hn : 0 < n) :
    conclusion_hydrogenic_strict_twolevel_gauge_tower_statement n := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a l
    constructor
    · intro h
      rcases a with ⟨l', mu, spin⟩
      change l' = l at h
      subst l
      exact ⟨mu, rfl⟩
    · rintro ⟨mu, hmu⟩
      exact congrArg Sigma.fst hmu
  · intro l mu₁ mu₂ hne a hmu₁ hmu₂
    have hclasses :
        (⟨l, mu₁⟩ :
          conclusion_hydrogenic_strict_twolevel_gauge_tower_phaseblind_class n) =
          ⟨l, mu₂⟩ := hmu₁.symm.trans hmu₂
    cases hclasses
    exact hne rfl
  · intro l
    simp
  · intro l mu hmu
    simp [ne_of_gt hmu]

end Omega.Conclusion
