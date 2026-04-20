import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The three factors appearing in the toy-RH zeta-factorization package. -/
inductive ToyRhFactor where
  | shortPeriodic
  | tensorAA
  | minusA
  deriving DecidableEq, Repr

/-- Real part of the pole line contributed by each factor in the Dirichlet coordinate
`z = λ^{-s}`. The short periodic term and the `A ⊗ A` term live on the boundary lines,
while the `-A` term lives on the critical line `Re(s) = 1/2`. -/
def toyRhPoleRealPart : ToyRhFactor → ℝ
  | .shortPeriodic => 1
  | .tensorAA => 0
  | .minusA => (1 : ℝ) / 2

/-- The open strip `0 < Re(s) < 1`. -/
def toyRhOpenStrip (σ : ℝ) : Prop :=
  0 < σ ∧ σ < 1

/-- The boundary lines `Re(s) = 0` or `Re(s) = 1`. -/
def toyRhBoundaryLine (σ : ℝ) : Prop :=
  σ = 0 ∨ σ = 1

/-- The minus-`A` factor is the order-`2` torsion mode. -/
def toyRhTwoTorsionMode (F : ToyRhFactor) : Prop :=
  F = .minusA

lemma toyRh_shortPeriodic_boundary :
    toyRhBoundaryLine (toyRhPoleRealPart .shortPeriodic) := by
  right
  simp [toyRhPoleRealPart]

lemma toyRh_tensorAA_boundary :
    toyRhBoundaryLine (toyRhPoleRealPart .tensorAA) := by
  left
  simp [toyRhPoleRealPart]

/-- In the toy-RH factorization, the short periodic factor and the `A ⊗ A` factor only
contribute boundary-line poles, so every pole in the open strip comes from the `-A` factor;
that sign twist is exactly the order-`2` torsion mode.
    prop:pom-toy-rh-2torsion-source -/
theorem paper_pom_toy_rh_2torsion_source :
    (∀ F : ToyRhFactor, toyRhOpenStrip (toyRhPoleRealPart F) → F = .minusA) ∧
      toyRhTwoTorsionMode .minusA := by
  refine ⟨?_, rfl⟩
  intro F hF
  cases F with
  | shortPeriodic =>
      exfalso
      rcases hF with ⟨h0, h1⟩
      have : ¬ ((1 : ℝ) < 1) := by norm_num
      exact this h1
  | tensorAA =>
      exfalso
      rcases hF with ⟨h0, _h1⟩
      have : ¬ ((0 : ℝ) < 0) := by norm_num
      exact this h0
  | minusA =>
      rfl

end

end Omega.POM
