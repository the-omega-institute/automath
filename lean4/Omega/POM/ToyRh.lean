import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.ToyRh2TorsionSource

namespace Omega.POM

noncomputable section

/-- The explicit Dirichlet pole sources listed in the toy-RH theorem. -/
inductive ToyRhPoleSource where
  | one
  | plusLambda
  | minusLambda
  | lambdaSquared
  | phiCubed
  | minusPhi
  deriving DecidableEq, Repr

/-- Real parts of the Dirichlet pole lines attached to the explicit pole sources
`r ∈ {1, ±λ, λ², φ³, -φ}`. -/
def toyRhPoleSourceRealPart : ToyRhPoleSource → ℝ
  | .one => 1
  | .plusLambda => 0
  | .minusLambda => 0
  | .lambdaSquared => -1
  | .phiCubed => -((1 : ℝ) / 2)
  | .minusPhi => (1 : ℝ) / 2

/-- The strip source `r = -φ` is the same minus-`A` / order-`2` torsion source appearing in
`ToyRh2TorsionSource`. The remaining sources lie on the boundary or farther left. -/
def ToyRhPoleSource.associatedFactor : ToyRhPoleSource → ToyRhFactor
  | .one => .shortPeriodic
  | .plusLambda | .minusLambda | .lambdaSquared | .phiCubed => .tensorAA
  | .minusPhi => .minusA

/-- A finite package of explicit Dirichlet pole sources. -/
structure ToyRhPoleData where
  support : Finset ToyRhPoleSource

/-- The package records the real parts arising from its listed pole sources. -/
def ToyRhPoleData.pole_real_part (D : ToyRhPoleData) (σ : ℝ) : Prop :=
  ∃ S ∈ D.support, σ = toyRhPoleSourceRealPart S

/-- Open-strip poles are exactly the recorded poles whose real part lies in `0 < σ < 1`. -/
def ToyRhPoleData.open_strip_pole (D : ToyRhPoleData) (σ : ℝ) : Prop :=
  D.pole_real_part σ ∧ toyRhOpenStrip σ

lemma toyRhPoleSource_open_strip_eq_half {S : ToyRhPoleSource} {σ : ℝ}
    (hσ : σ = toyRhPoleSourceRealPart S) (hopen : toyRhOpenStrip σ) :
    σ = (1 : ℝ) / 2 := by
  cases S with
  | one =>
      rcases hopen with ⟨_, hlt⟩
      simp [hσ, toyRhPoleSourceRealPart] at hlt
  | plusLambda =>
      rcases hopen with ⟨hgt, _⟩
      simp [hσ, toyRhPoleSourceRealPart] at hgt
  | minusLambda =>
      rcases hopen with ⟨hgt, _⟩
      simp [hσ, toyRhPoleSourceRealPart] at hgt
  | lambdaSquared =>
      rcases hopen with ⟨hgt, _⟩
      have : ¬ ((0 : ℝ) < -1) := by norm_num
      exact False.elim <| this (by simpa [hσ, toyRhPoleSourceRealPart] using hgt)
  | phiCubed =>
      rcases hopen with ⟨hgt, _⟩
      have : ¬ ((0 : ℝ) < -((1 : ℝ) / 2)) := by norm_num
      exact False.elim <| this (by simpa [hσ, toyRhPoleSourceRealPart] using hgt)
  | minusPhi =>
      have hfactor_strip :
          toyRhOpenStrip (toyRhPoleRealPart (ToyRhPoleSource.associatedFactor .minusPhi)) := by
        simpa [hσ, ToyRhPoleSource.associatedFactor, toyRhPoleSourceRealPart, toyRhPoleRealPart]
          using hopen
      have _hminusA :
          ToyRhPoleSource.associatedFactor .minusPhi = ToyRhFactor.minusA :=
        (paper_pom_toy_rh_2torsion_source).1 _ hfactor_strip
      simpa [toyRhPoleSourceRealPart] using hσ

/-- Paper label: `thm:pom-toy-rh`. -/
theorem paper_pom_toy_rh (D : ToyRhPoleData) :
    (∀ σ : ℝ,
        D.pole_real_part σ →
          σ = 1 ∨ σ = (1 : ℝ) / 2 ∨ σ = 0 ∨ σ = -((1 : ℝ) / 2) ∨ σ = -1) ∧
      (∀ σ : ℝ, D.open_strip_pole σ → σ = (1 : ℝ) / 2) := by
  refine ⟨?_, ?_⟩
  · intro σ hσ
    rcases hσ with ⟨S, _, rfl⟩
    cases S <;> simp [toyRhPoleSourceRealPart]
  · intro σ hσ
    rcases hσ with ⟨hreal, hopen⟩
    rcases hreal with ⟨S, _, hS⟩
    exact toyRhPoleSource_open_strip_eq_half hS hopen

end

end Omega.POM
