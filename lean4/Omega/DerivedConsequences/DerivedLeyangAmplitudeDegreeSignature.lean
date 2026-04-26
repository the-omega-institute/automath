import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation

namespace Omega.DerivedConsequences

/-- The rational norm coming from the constant-term ratio of the Lee--Yang amplitude-square cubic.
-/
def derived_leyang_amplitude_degree_signature_rational_norm : ℚ :=
  -((592 : ℚ) / 81)

/-- The displayed even sextic attached to the Lee--Yang amplitude constant. -/
def derived_leyang_amplitude_degree_signature_sextic_eval (x : ℝ) : ℝ :=
  162 * x ^ 6 + 1593 * x ^ 4 + 1998 * x ^ 2 + 1184

/-- The quadratic extension over the cubic package has the displayed degree. -/
def derived_leyang_amplitude_degree_signature_field_degree : ℕ :=
  6

/-- The field is recorded with the totally imaginary signature `(0, 3)`. -/
def derived_leyang_amplitude_degree_signature_signature : ℕ × ℕ :=
  (0, 3)

/-- Concrete Lee--Yang amplitude-degree/signature package. The rational norm is negative and hence
not a square, the shared quadratic resolvent remains `-111`, the quadratic-over-cubic tower has
degree `6`, and the displayed even sextic is strictly positive on `ℝ`, matching the totally
imaginary signature placeholder `(0, 3)`. -/
def derived_leyang_amplitude_degree_signature_statement : Prop :=
  derived_leyang_amplitude_degree_signature_rational_norm = -((592 : ℚ) / 81) ∧
    derived_leyang_amplitude_degree_signature_rational_norm < 0 ∧
    ¬ IsSquare derived_leyang_amplitude_degree_signature_rational_norm ∧
    Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 ∧
    derived_leyang_amplitude_degree_signature_field_degree = 6 ∧
    derived_leyang_amplitude_degree_signature_signature = (0, 3) ∧
    ∀ x : ℝ, 0 < derived_leyang_amplitude_degree_signature_sextic_eval x

/-- Paper label: `thm:derived-leyang-amplitude-degree-signature`. -/
theorem paper_derived_leyang_amplitude_degree_signature :
    derived_leyang_amplitude_degree_signature_statement := by
  refine ⟨rfl, by norm_num [derived_leyang_amplitude_degree_signature_rational_norm], ?_, ?_,
    rfl, rfl, ?_⟩
  · intro hsquare
    rcases hsquare with ⟨q, hq⟩
    have hnonneg : 0 ≤ derived_leyang_amplitude_degree_signature_rational_norm := by
      simpa [pow_two, hq] using sq_nonneg q
    norm_num [derived_leyang_amplitude_degree_signature_rational_norm] at hnonneg
  · exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.2.2.2.2
  · intro x
    unfold derived_leyang_amplitude_degree_signature_sextic_eval
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x ^ 3)]

end Omega.DerivedConsequences
