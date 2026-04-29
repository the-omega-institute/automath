import Mathlib.Tactic

namespace Omega.Zeta

/-- Source affine Weierstrass model `y^2 = u (u^2 + A u + B)` carrying the rational `2`-torsion
point `Q = (0, 0)`. -/
def xi_j_discriminant_2isogeny_velu_sourceEquation (A B u y : ℚ) : Prop :=
  y ^ 2 = u * (u ^ 2 + A * u + B)

/-- The explicit Vélu `x`-coordinate on the quotient. -/
def xi_j_discriminant_2isogeny_velu_xRaw (B u : ℚ) : ℚ :=
  u + B / u

/-- The shifted target `x`-coordinate putting the quotient into the standard Weierstrass form
`x' (x'^2 - 2 A x' + (A^2 - 4 B))`. -/
def xi_j_discriminant_2isogeny_velu_xTarget (A B u : ℚ) : ℚ :=
  A + xi_j_discriminant_2isogeny_velu_xRaw B u

/-- The explicit Vélu `y`-coordinate on the quotient. -/
def xi_j_discriminant_2isogeny_velu_yTarget (B u y : ℚ) : ℚ :=
  y * (1 - B / u ^ 2)

/-- Target affine Weierstrass model for the quotient. -/
def xi_j_discriminant_2isogeny_velu_targetEquation (A B x y : ℚ) : Prop :=
  y ^ 2 = x * (x ^ 2 - 2 * A * x + (A ^ 2 - 4 * B))

/-- The explicit `Q`-translate on the source: `(u, y) ↦ (B / u, -B y / u^2)`. -/
def xi_j_discriminant_2isogeny_velu_partnerPoint (B u y : ℚ) : ℚ × ℚ :=
  (B / u, -(B * y) / u ^ 2)

/-- Concrete Vélu package: `(0, 0)` is the `2`-torsion kernel point, the explicit quotient
coordinates land on the target Weierstrass model, and the partner point differing by `Q` has the
same target coordinates, packaging the degree-`2` quotient. -/
def xi_j_discriminant_2isogeny_velu_statement : Prop :=
  ∀ A B u y : ℚ, B ≠ 0 → u ≠ 0 →
    xi_j_discriminant_2isogeny_velu_sourceEquation A B u y →
      xi_j_discriminant_2isogeny_velu_sourceEquation A B 0 0 ∧
        xi_j_discriminant_2isogeny_velu_targetEquation A B
          (xi_j_discriminant_2isogeny_velu_xTarget A B u)
          (xi_j_discriminant_2isogeny_velu_yTarget B u y) ∧
        xi_j_discriminant_2isogeny_velu_xTarget A B (B / u) =
          xi_j_discriminant_2isogeny_velu_xTarget A B u ∧
        xi_j_discriminant_2isogeny_velu_yTarget B (B / u)
            (xi_j_discriminant_2isogeny_velu_partnerPoint B u y).2 =
          xi_j_discriminant_2isogeny_velu_yTarget B u y

lemma xi_j_discriminant_2isogeny_velu_targetEquation_of_source
    {A B u y : ℚ} (hu : u ≠ 0)
    (hsrc : xi_j_discriminant_2isogeny_velu_sourceEquation A B u y) :
    xi_j_discriminant_2isogeny_velu_targetEquation A B
      (xi_j_discriminant_2isogeny_velu_xTarget A B u)
      (xi_j_discriminant_2isogeny_velu_yTarget B u y) := by
  have hy2 : y ^ 2 = u ^ 3 + A * u ^ 2 + B * u := by
    dsimp [xi_j_discriminant_2isogeny_velu_sourceEquation] at hsrc
    nlinarith [hsrc]
  dsimp [xi_j_discriminant_2isogeny_velu_targetEquation,
    xi_j_discriminant_2isogeny_velu_xTarget, xi_j_discriminant_2isogeny_velu_xRaw,
    xi_j_discriminant_2isogeny_velu_yTarget]
  field_simp [hu]
  nlinarith [hy2]

lemma xi_j_discriminant_2isogeny_velu_x_partner
    {A B u : ℚ} (hB : B ≠ 0) (hu : u ≠ 0) :
    xi_j_discriminant_2isogeny_velu_xTarget A B (B / u) =
      xi_j_discriminant_2isogeny_velu_xTarget A B u := by
  dsimp [xi_j_discriminant_2isogeny_velu_xTarget, xi_j_discriminant_2isogeny_velu_xRaw]
  field_simp [hB, hu]
  ring

lemma xi_j_discriminant_2isogeny_velu_y_partner
    {B u y : ℚ} (hB : B ≠ 0) (hu : u ≠ 0) :
    xi_j_discriminant_2isogeny_velu_yTarget B (B / u)
        (xi_j_discriminant_2isogeny_velu_partnerPoint B u y).2 =
      xi_j_discriminant_2isogeny_velu_yTarget B u y := by
  dsimp [xi_j_discriminant_2isogeny_velu_yTarget, xi_j_discriminant_2isogeny_velu_partnerPoint]
  field_simp [hB, hu]
  ring_nf

/-- Paper label: `thm:xi-j-discriminant-2isogeny-velu`. The point `Q = (0, 0)` is the explicit
kernel point, the Vélu formulas produce a quotient point on the target Weierstrass model, and the
partner point differing by `Q` has the same target coordinates, packaging the degree-`2` quotient
behavior. -/
theorem paper_xi_j_discriminant_2isogeny_velu : xi_j_discriminant_2isogeny_velu_statement := by
  intro A B u y hB hu hsrc
  refine ⟨by
    dsimp [xi_j_discriminant_2isogeny_velu_sourceEquation]
    ring, ?_, ?_, ?_⟩
  · exact xi_j_discriminant_2isogeny_velu_targetEquation_of_source hu hsrc
  · exact xi_j_discriminant_2isogeny_velu_x_partner hB hu
  · exact xi_j_discriminant_2isogeny_velu_y_partner hB hu

end Omega.Zeta
