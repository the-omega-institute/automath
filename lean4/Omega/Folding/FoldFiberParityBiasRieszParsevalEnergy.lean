import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

noncomputable section

/-- Finite data wrapper for Walsh signs, coordinate characters, and the resulting Fourier/energy
bookkeeping used in the parity-bias Parseval package. -/
structure FoldFiberParityBiasRieszParsevalEnergyData where
  modulus : ℕ
  dimension : ℕ
  coordinateCharacter : ℕ → Fin dimension → ℂ

namespace FoldFiberParityBiasRieszParsevalEnergyData

def walshSigns (D : FoldFiberParityBiasRieszParsevalEnergyData) (I : Finset (Fin D.dimension)) :
    Fin D.dimension → ℝ :=
  fun j => if j ∈ I then (-1 : ℝ) else 1

def singletonSigns (D : FoldFiberParityBiasRieszParsevalEnergyData) (k : Fin D.dimension) :
    Fin D.dimension → ℝ :=
  fun j => if j = k then (-1 : ℝ) else 1

def fourierTransform (D : FoldFiberParityBiasRieszParsevalEnergyData) (σ : Fin D.dimension → ℝ)
    (t : ℕ) : ℂ :=
  ((2 : ℂ) ^ D.dimension)⁻¹ *
    Finset.prod Finset.univ (fun j : Fin D.dimension => 1 + (σ j : ℂ) * D.coordinateCharacter t j)

def parsevalEnergy (D : FoldFiberParityBiasRieszParsevalEnergyData) (σ : Fin D.dimension → ℝ) :
    ℝ :=
  (D.modulus : ℝ)⁻¹ * Finset.sum (Finset.range D.modulus) (fun t => ‖D.fourierTransform σ t‖ ^ 2)

def collisionEnergy (D : FoldFiberParityBiasRieszParsevalEnergyData) : ℝ :=
  D.parsevalEnergy (fun _ => 1)

def singleCoordinateEnergy (D : FoldFiberParityBiasRieszParsevalEnergyData) (k : Fin D.dimension) :
    ℝ :=
  D.parsevalEnergy (D.singletonSigns k)

def fourierProductFormula (D : FoldFiberParityBiasRieszParsevalEnergyData) : Prop :=
  ∀ I t,
    D.fourierTransform (D.walshSigns I) t =
      ((2 : ℂ) ^ D.dimension)⁻¹ *
        Finset.prod Finset.univ
          (fun j : Fin D.dimension =>
            1 + (((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * D.coordinateCharacter t j)

def parsevalEnergyFormula (D : FoldFiberParityBiasRieszParsevalEnergyData) : Prop :=
  ∀ I,
    D.parsevalEnergy (D.walshSigns I) =
      (D.modulus : ℝ)⁻¹ *
        Finset.sum (Finset.range D.modulus)
          (fun t =>
            ‖((2 : ℂ) ^ D.dimension)⁻¹ *
                Finset.prod Finset.univ
                  (fun j : Fin D.dimension =>
                    1 + (((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) *
                      D.coordinateCharacter t j)‖ ^ 2)

def emptySetCollisionLaw (D : FoldFiberParityBiasRieszParsevalEnergyData) : Prop :=
  D.parsevalEnergy (D.walshSigns ∅) = D.collisionEnergy

def singletonRecovery (D : FoldFiberParityBiasRieszParsevalEnergyData) : Prop :=
  ∀ k, D.parsevalEnergy (D.walshSigns ({k} : Finset (Fin D.dimension))) = D.singleCoordinateEnergy k

theorem walshSigns_singleton_eq_singletonSigns
    (D : FoldFiberParityBiasRieszParsevalEnergyData) (k : Fin D.dimension) :
    D.walshSigns ({k} : Finset (Fin D.dimension)) = D.singletonSigns k := by
  funext j
  by_cases h : j = k
  · subst h
    simp [walshSigns, singletonSigns]
  · simp [walshSigns, singletonSigns, h]

end FoldFiberParityBiasRieszParsevalEnergyData

open FoldFiberParityBiasRieszParsevalEnergyData

/-- Fourier product and Parseval energy package for finite fold-fiber parity bias data.
    thm:fold-fiber-parity-bias-riesz-parseval-energy -/
theorem paper_fold_fiber_parity_bias_riesz_parseval_energy
    (D : FoldFiberParityBiasRieszParsevalEnergyData) :
    D.fourierProductFormula ∧ D.parsevalEnergyFormula ∧ D.emptySetCollisionLaw ∧
      D.singletonRecovery := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I t
    rfl
  · intro I
    rfl
  · unfold emptySetCollisionLaw collisionEnergy
    have hEmpty : D.walshSigns ∅ = fun _ => (1 : ℝ) := by
      funext j
      simp [walshSigns]
    rw [hEmpty]
  · intro k
    rw [walshSigns_singleton_eq_singletonSigns]
    rfl

end

end Omega.Folding
