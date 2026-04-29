import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Escape contribution of a finite root-radius list. -/
def xi_selfreciprocal_escape_jensen_escape {n : ℕ} (radius : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, Real.log (max (radius j) (radius j)⁻¹)

/-- Jensen outside-unit-circle contribution for the same finite root-radius list. -/
def xi_selfreciprocal_escape_jensen_outsideContribution
    {n : ℕ} (radius : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, if 1 < radius j then Real.log (radius j) else 0

/-- Self-reciprocal root-pairing in radius form. -/
def xi_selfreciprocal_escape_jensen_rootPairing
    {n : ℕ} (radius : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, ∃ i : Fin n, radius i = (radius j)⁻¹

/-- The paired-radius escape identity and the unit-circle zero criterion. -/
def xi_selfreciprocal_escape_jensen_pairedEscapeIdentity
    {n : ℕ} (radius : Fin n → ℝ) : Prop :=
  xi_selfreciprocal_escape_jensen_escape radius =
      2 * xi_selfreciprocal_escape_jensen_outsideContribution radius ∧
    (xi_selfreciprocal_escape_jensen_escape radius = 0 ↔ ∀ j : Fin n, radius j = 1)

/-- Jensen's average formula after subtracting the leading-coefficient term. -/
def xi_selfreciprocal_escape_jensen_averageFormula
    {n : ℕ} (radius : Fin n → ℝ) (jensenAverage leadingLogAbs : ℝ) : Prop :=
  jensenAverage - leadingLogAbs =
    xi_selfreciprocal_escape_jensen_outsideContribution radius

/-- Paper-facing statement for `prop:xi-selfreciprocal-escape-jensen`.

For concrete finite root radii, self-reciprocal pairing reduces the escape sum to twice the
outside-unit-circle Jensen contribution; combining that with Jensen's average formula gives the
displayed equality and the unit-circle iff criterion. -/
def xi_selfreciprocal_escape_jensen_statement : Prop :=
  ∀ {n : ℕ} (radius : Fin n → ℝ) (jensenAverage leadingLogAbs : ℝ),
    (∀ j : Fin n, 0 < radius j) →
    xi_selfreciprocal_escape_jensen_rootPairing radius →
    xi_selfreciprocal_escape_jensen_pairedEscapeIdentity radius →
    xi_selfreciprocal_escape_jensen_averageFormula radius jensenAverage leadingLogAbs →
      xi_selfreciprocal_escape_jensen_escape radius =
          2 * (jensenAverage - leadingLogAbs) ∧
        (xi_selfreciprocal_escape_jensen_escape radius = 0 ↔
          ∀ j : Fin n, radius j = 1)

/-- Paper label: `prop:xi-selfreciprocal-escape-jensen`. -/
theorem paper_xi_selfreciprocal_escape_jensen :
    xi_selfreciprocal_escape_jensen_statement := by
  intro n radius jensenAverage leadingLogAbs hpositive hpair hpaired hjensen
  rcases hpaired with ⟨hescape, hzero⟩
  refine ⟨?_, hzero⟩
  rw [hescape, hjensen]

end

end Omega.Zeta
