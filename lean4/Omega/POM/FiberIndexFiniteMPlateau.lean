import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Total weight carried by a finite plateau set. -/
def plateauWeightSum {α : Type*} (plateau : Finset α) (weight : α → ℝ) : ℝ :=
  plateau.sum weight

/-- Concrete finite-`m` plateau package. The fields record the finite pushforward weights on a
finite layer, the Chebyshev control on the bad set, the resulting plateau mass bookkeeping, and
the pointwise plateau bound needed to turn mass into cardinality. -/
structure POMSpectrumFiniteMPlateauData where
  α : Type*
  instFintype : Fintype α
  instDecEq : DecidableEq α
  m : ℕ
  mu : ℝ
  eps : ℝ
  sigmaSq : ℝ
  weight : α → ℝ
  plateau : Finset α
  plateauMass : ℝ
  badMass : ℝ
  plateauMass_eq : plateauMass = plateauWeightSum plateau weight
  mass_split : plateauMass + badMass = 1
  chebyshev_badMass : badMass ≤ sigmaSq / eps ^ 2
  plateau_pointwise :
    ∀ x ∈ plateau, weight x ≤ Real.exp (m * (mu + eps)) / (2 ^ m : ℝ)

attribute [instance] POMSpectrumFiniteMPlateauData.instFintype
attribute [instance] POMSpectrumFiniteMPlateauData.instDecEq

namespace POMSpectrumFiniteMPlateauData

/-- The plateau mass lower bound obtained from the Chebyshev estimate on the bad set. -/
def plateauMassLowerBound (D : POMSpectrumFiniteMPlateauData) : Prop :=
  1 - D.sigmaSq / D.eps ^ 2 ≤ plateauWeightSum D.plateau D.weight

/-- The plateau cardinality lower bound obtained by combining the mass lower bound with the
pointwise plateau estimate. -/
def plateauCardinalityLowerBound (D : POMSpectrumFiniteMPlateauData) : Prop :=
  (1 - D.sigmaSq / D.eps ^ 2) /
      (Real.exp (D.m * (D.mu + D.eps)) / (2 ^ D.m : ℝ)) ≤
    (D.plateau.card : ℝ)

/-- Paper-facing finite-`m` plateau statement. -/
def statement (D : POMSpectrumFiniteMPlateauData) : Prop :=
  D.plateauMassLowerBound ∧ D.plateauCardinalityLowerBound

end POMSpectrumFiniteMPlateauData

open POMSpectrumFiniteMPlateauData

/-- Finite-`m` plateau lower bound: the bad set has Chebyshev-controlled mass, so the plateau has
mass at least `1 - σ_m² / ε²`; on the plateau every weight is at most
`exp (m (μ_m + ε)) / 2^m`, hence the plateau cardinality enjoys the corresponding lower bound.
    prop:pom-spectrum-finite-m-plateau -/
theorem paper_pom_spectrum_finite_m_plateau (D : POMSpectrumFiniteMPlateauData) : D.statement := by
  dsimp [POMSpectrumFiniteMPlateauData.statement, POMSpectrumFiniteMPlateauData.plateauMassLowerBound,
    POMSpectrumFiniteMPlateauData.plateauCardinalityLowerBound]
  have hMassLower' : 1 - D.sigmaSq / D.eps ^ 2 ≤ D.plateauMass := by
    linarith [D.mass_split, D.chebyshev_badMass]
  let B : ℝ := Real.exp (D.m * (D.mu + D.eps)) / (2 ^ D.m : ℝ)
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hMassUpper : D.plateauMass ≤ (D.plateau.card : ℝ) * B := by
    rw [D.plateauMass_eq]
    calc
      plateauWeightSum D.plateau D.weight ≤ plateauWeightSum D.plateau (fun _ => B) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact D.plateau_pointwise x hx
      _ = (D.plateau.card : ℝ) * B := by
        simp [plateauWeightSum, B, mul_comm, Finset.sum_const]
  have hMul : 1 - D.sigmaSq / D.eps ^ 2 ≤ (D.plateau.card : ℝ) * B := by
    linarith [hMassLower', hMassUpper]
  have hInv_nonneg : 0 ≤ 1 / B := by
    positivity
  have hCardMul : (1 - D.sigmaSq / D.eps ^ 2) * (1 / B) ≤ (D.plateau.card : ℝ) * B * (1 / B) := by
    exact mul_le_mul_of_nonneg_right hMul hInv_nonneg
  constructor
  · simpa [D.plateauMass_eq] using hMassLower'
  · simpa [div_eq_mul_inv, B, mul_assoc, hB_pos.ne'] using hCardMul

end Omega.POM
