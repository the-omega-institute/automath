import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete arity parameter for the finite product-character model. -/
abbrev xi_time_part62af_cross_anom_interaction_degree_data := ℕ

/-- Boolean finite product characters on `D` coordinates. -/
abbrev xi_time_part62af_cross_anom_interaction_degree_character
    (D : xi_time_part62af_cross_anom_interaction_degree_data) :=
  Fin D → Bool

/-- Coordinate restriction to a finite support, with the neutral character represented by `false`. -/
def xi_time_part62af_cross_anom_interaction_degree_restrict
    (D : xi_time_part62af_cross_anom_interaction_degree_data) (S : Finset (Fin D))
    (χ : xi_time_part62af_cross_anom_interaction_degree_character D) :
    xi_time_part62af_cross_anom_interaction_degree_character D :=
  fun i => if i ∈ S then χ i else false

/-- Möbius finite-difference anomaly on a support `S`. -/
def xi_time_part62af_cross_anom_interaction_degree_anomaly
    (D : xi_time_part62af_cross_anom_interaction_degree_data)
    (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ)
    (S : Finset (Fin D)) (χ : xi_time_part62af_cross_anom_interaction_degree_character D) :
    ℤ :=
  Finset.sum S.powerset fun T =>
    (-1 : ℤ) ^ (S.card - T.card) *
      f (xi_time_part62af_cross_anom_interaction_degree_restrict D T χ)

/-- A support contributes to the interaction degree exactly when some anomaly on it is nonzero. -/
def xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport
    (D : xi_time_part62af_cross_anom_interaction_degree_data)
    (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ)
    (S : Finset (Fin D)) : Prop :=
  ∃ χ : xi_time_part62af_cross_anom_interaction_degree_character D,
    xi_time_part62af_cross_anom_interaction_degree_anomaly D f S χ ≠ 0

/-- The finite maximum support size carrying a nonzero anomaly component. -/
noncomputable def xi_time_part62af_cross_anom_interaction_degree_degree
    (D : xi_time_part62af_cross_anom_interaction_degree_data)
    (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ) : ℕ := by
  classical
  exact
    (Finset.univ.filter
        (fun S : Finset (Fin D) =>
          xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D f S)).sup
      Finset.card

/-- Low-order interaction means all anomalies on supports larger than `r` vanish. -/
def xi_time_part62af_cross_anom_interaction_degree_lowOrder
    (D : xi_time_part62af_cross_anom_interaction_degree_data) (r : ℕ)
    (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ) : Prop :=
  ∀ (S : Finset (Fin D)) (χ : xi_time_part62af_cross_anom_interaction_degree_character D),
    r < S.card → xi_time_part62af_cross_anom_interaction_degree_anomaly D f S χ = 0

/-- Concrete conclusion: bounded interaction degree is equivalent to vanishing high anomalies. -/
noncomputable def xi_time_part62af_cross_anom_interaction_degree_conclusion
    (D : xi_time_part62af_cross_anom_interaction_degree_data) : Prop := by
  classical
  exact
    ∀ (r : ℕ) (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ),
      (xi_time_part62af_cross_anom_interaction_degree_degree D f ≤ r ↔
          xi_time_part62af_cross_anom_interaction_degree_lowOrder D r f) ∧
        xi_time_part62af_cross_anom_interaction_degree_degree D f =
          (Finset.univ.filter
              (fun S : Finset (Fin D) =>
                xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D f S)).sup
            Finset.card

/-- Paper label: `thm:xi-time-part62af-cross-anom-interaction-degree`. -/
theorem paper_xi_time_part62af_cross_anom_interaction_degree
    (D : xi_time_part62af_cross_anom_interaction_degree_data) :
    xi_time_part62af_cross_anom_interaction_degree_conclusion D := by
  classical
  intro r f
  constructor
  · constructor
    · intro hdegree S χ hlarge
      by_contra hnonzero
      have hsupport :
          xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D f S := by
        exact ⟨χ, hnonzero⟩
      have hmem :
          S ∈ Finset.univ.filter
            (fun S : Finset (Fin D) =>
              xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D f S) := by
        simp [hsupport]
      have hcard_le_degree :
          S.card ≤ xi_time_part62af_cross_anom_interaction_degree_degree D f := by
        unfold xi_time_part62af_cross_anom_interaction_degree_degree
        exact Finset.le_sup hmem
      omega
    · intro hlow
      unfold xi_time_part62af_cross_anom_interaction_degree_degree
      rw [Finset.sup_le_iff]
      intro S hS
      by_cases hcard : S.card ≤ r
      · exact hcard
      · have hlarge : r < S.card := Nat.lt_of_not_ge hcard
        have hsupport :
            xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D f S := by
          simpa using hS
        rcases hsupport with ⟨χ, hχ⟩
        exact (hχ (hlow S χ hlarge)).elim
  · rfl

end Omega.Zeta
