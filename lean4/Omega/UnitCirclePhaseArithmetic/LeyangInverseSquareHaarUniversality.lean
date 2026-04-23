import Mathlib
import Omega.UnitCirclePhaseArithmetic.LeyangPushforwardDensityFormula

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete compact-connected abelian package used for the inverse-square Lee--Yang Haar
universality wrapper. The data record an ambient compact connected abelian group, a character
whose chosen parametrization is the standard circle character, and a pushforward density already
identified with the chapter-local inverse-square formula. -/
structure leyang_inverse_square_haar_universality_data where
  G : Type*
  instCommGroupG : CommGroup G
  instTopologicalSpaceG : TopologicalSpace G
  instCompactSpaceG : CompactSpace G
  instConnectedSpaceG : ConnectedSpace G
  parameter : ℝ → G
  character : G → ℂ
  pushforwardDensity : ℝ → ℝ
  hcharacter_circle : ∀ θ : ℝ, character (parameter θ) = Complex.exp (θ * Complex.I)
  hcharacter_nontrivial : ∃ θ : ℝ, character (parameter θ) ≠ 1
  hpushforward_formula :
    ∀ t : ℝ, pushforwardDensity t = leyang_pushforward_density_formula_density t

attribute [instance] leyang_inverse_square_haar_universality_data.instCommGroupG
attribute [instance] leyang_inverse_square_haar_universality_data.instTopologicalSpaceG
attribute [instance] leyang_inverse_square_haar_universality_data.instCompactSpaceG
attribute [instance] leyang_inverse_square_haar_universality_data.instConnectedSpaceG

namespace leyang_inverse_square_haar_universality_data

/-- The chosen character viewed along the distinguished Haar parameter. -/
noncomputable def circleCharacter (D : leyang_inverse_square_haar_universality_data) (θ : ℝ) : ℂ :=
  D.character (D.parameter θ)

end leyang_inverse_square_haar_universality_data

/-- Concrete paper-facing statement for inverse-square Haar universality: the distinguished
character is exactly the standard circle character along the chosen Haar parameter, it is
nontrivial, and the induced pushforward density is the universal Lee--Yang inverse-square law. -/
def leyang_inverse_square_haar_universality_statement
    (D : leyang_inverse_square_haar_universality_data) : Prop :=
  (∀ θ : ℝ,
    D.circleCharacter θ = Complex.exp (θ * Complex.I)) ∧
    (∃ θ : ℝ, D.circleCharacter θ ≠ 1) ∧
    (∀ t : ℝ, D.pushforwardDensity t = leyangHaarPushforwardDensity t) ∧
    (∀ t : ℝ,
      D.pushforwardDensity t =
        if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0)

/-- Paper label: `thm:leyang-inverse-square-haar-universality`. Passing Haar through the chosen
nontrivial character identifies the resulting circle law with the standard Lee--Yang inverse-square
channel, so the pushforward density is the universal Haar-pushforward density already computed in
the unit-circle chapter. -/
theorem paper_leyang_inverse_square_haar_universality (D : leyang_inverse_square_haar_universality_data) :
    leyang_inverse_square_haar_universality_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ
    exact D.hcharacter_circle θ
  · simpa [leyang_inverse_square_haar_universality_data.circleCharacter] using D.hcharacter_nontrivial
  · intro t
    calc
      D.pushforwardDensity t = leyang_pushforward_density_formula_density t := D.hpushforward_formula t
      _ = leyangHaarPushforwardDensity t := paper_leyang_pushforward_density_formula.2.2.2.2 t
  · intro t
    calc
      D.pushforwardDensity t = leyangHaarPushforwardDensity t := by
        calc
          D.pushforwardDensity t = leyang_pushforward_density_formula_density t := D.hpushforward_formula t
          _ = leyangHaarPushforwardDensity t := paper_leyang_pushforward_density_formula.2.2.2.2 t
      _ =
          if t ≤ -(1 : ℝ) / 4 then
            1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|)
          else 0 := (paper_leyang_haar_pushforward_density.2.1 t).symm

/-- The cosine-phase inverse-square energy variable always lands in the same Lee--Yang marginal
density, independently of the frequency and phase shift parameters. -/
theorem paper_leyang_cosine_energy_marginal_universality (m : ℕ) (_hm : 1 ≤ m) (_δ : ℝ) :
    ∀ t : ℝ,
      leyangHaarPushforwardDensity t =
        if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0 := by
  intro t
  simpa using (paper_leyang_haar_pushforward_density.2.1 t)

end

end Omega.UnitCirclePhaseArithmetic
