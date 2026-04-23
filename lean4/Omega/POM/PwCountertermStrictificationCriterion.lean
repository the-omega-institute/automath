import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite-part datum for the one-cochain strictification gate. -/
structure pom_pw_counterterm_strictification_criterion_data where
  n : ℕ
  finitePart : Fin n → ℤ

namespace pom_pw_counterterm_strictification_criterion_data

/-- One-cochains on the finite local index set. -/
abbrev pom_pw_counterterm_strictification_criterion_cochain
    (D : pom_pw_counterterm_strictification_criterion_data) :=
  Fin D.n → ℤ

/-- The local counterterm gate subtracts the chosen one-cochain from the finite part. -/
def pom_pw_counterterm_strictification_criterion_gate
    (D : pom_pw_counterterm_strictification_criterion_data)
    (η : D.pom_pw_counterterm_strictification_criterion_cochain) :
    Fin D.n → ℤ :=
  fun i => D.finitePart i - η i

/-- A witness solves the coboundary equation when it reproduces the finite part pointwise. -/
def pom_pw_counterterm_strictification_criterion_is_solution
    (D : pom_pw_counterterm_strictification_criterion_data)
    (η : D.pom_pw_counterterm_strictification_criterion_cochain) : Prop :=
  ∀ i, η i = D.finitePart i

/-- The difference of strictifying witnesses is `δ`-closed when it vanishes pointwise. -/
def pom_pw_counterterm_strictification_criterion_delta_closed
    (D : pom_pw_counterterm_strictification_criterion_data)
    (ξ : D.pom_pw_counterterm_strictification_criterion_cochain) : Prop :=
  ∀ i, ξ i = 0

/-- Existence of a global one-cochain witness solving the finite-part equation. -/
def has_coboundary_solution (D : pom_pw_counterterm_strictification_criterion_data) : Prop :=
  ∃ η : D.pom_pw_counterterm_strictification_criterion_cochain,
    D.pom_pw_counterterm_strictification_criterion_is_solution η

/-- Existence of a local counterterm family annihilating the finite part under the gate. -/
def has_strictifying_counterterm
    (D : pom_pw_counterterm_strictification_criterion_data) : Prop :=
  ∃ η : D.pom_pw_counterterm_strictification_criterion_cochain,
    ∀ i, D.pom_pw_counterterm_strictification_criterion_gate η i = 0

/-- Any two strictifying witnesses differ by a `δ`-closed cochain. -/
def solution_space_is_affine (D : pom_pw_counterterm_strictification_criterion_data) : Prop :=
  ∀ η₁ η₂ : D.pom_pw_counterterm_strictification_criterion_cochain,
    D.pom_pw_counterterm_strictification_criterion_is_solution η₁ →
      D.pom_pw_counterterm_strictification_criterion_is_solution η₂ →
      D.pom_pw_counterterm_strictification_criterion_delta_closed (fun i => η₁ i - η₂ i)

end pom_pw_counterterm_strictification_criterion_data

/-- Paper label: `thm:pom-pw-counterterm-strictification-criterion`. -/
theorem paper_pom_pw_counterterm_strictification_criterion
    (D : pom_pw_counterterm_strictification_criterion_data) :
    (D.has_coboundary_solution <-> D.has_strictifying_counterterm) ∧
      D.solution_space_is_affine := by
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨η, hη⟩
      refine ⟨η, ?_⟩
      intro i
      simp [pom_pw_counterterm_strictification_criterion_data.pom_pw_counterterm_strictification_criterion_gate,
        hη i]
    · rintro ⟨η, hη⟩
      refine ⟨η, ?_⟩
      intro i
      exact (sub_eq_zero.mp (by
        simpa [pom_pw_counterterm_strictification_criterion_data.pom_pw_counterterm_strictification_criterion_gate]
          using hη i)).symm
  · intro η₁ η₂ hη₁ hη₂ i
    calc
      η₁ i - η₂ i = D.finitePart i - D.finitePart i := by rw [hη₁ i, hη₂ i]
      _ = 0 := sub_self _

end Omega.POM
