import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Omega.CircleDimension.S4V4PrymA2PolarizedIsogenyRigidity

namespace Omega.Zeta

open Matrix
open Omega.CircleDimension

/-- The Prym polarization matrix for the `S₃` endoscopic block. -/
def xiTerminalZmS3EndoscopicPrymPolarization : Matrix (Fin 2) (Fin 2) ℤ :=
  a2CartanForm

/-- The order-three deck transformation on the Prym lattice. -/
def xiTerminalZmS3EndoscopicDeckMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  s4v4StandardGenerator

/-- The Prym polarization identifies with the `A₂` Cartan form. -/
def xiTerminalZmS3EndoscopicPrymPolarizationIsA2 : Prop :=
  xiTerminalZmS3EndoscopicPrymPolarization = a2CartanForm

/-- The determinant-`3` polarization therefore has type `(1, 3)`. -/
def xiTerminalZmS3EndoscopicPrymPolarizationType : ℕ × ℕ :=
  (1, Int.natAbs xiTerminalZmS3EndoscopicPrymPolarization.det)

/-- The three-cycle acts by the standard `A₂` Coxeter element. -/
def xiTerminalZmS3EndoscopicDeckActsByA2Coxeter : Prop :=
  xiTerminalZmS3EndoscopicDeckMatrixᵀ * xiTerminalZmS3EndoscopicPrymPolarization *
      xiTerminalZmS3EndoscopicDeckMatrix =
    xiTerminalZmS3EndoscopicPrymPolarization ∧
    xiTerminalZmS3EndoscopicDeckMatrix.trace = -1 ∧
    xiTerminalZmS3EndoscopicDeckMatrix.charpoly = Polynomial.X ^ 2 + Polynomial.X + 1

private lemma xiTerminalZmS3EndoscopicDeckMatrix_det :
    xiTerminalZmS3EndoscopicDeckMatrix.det = 1 := by
  norm_num [xiTerminalZmS3EndoscopicDeckMatrix, s4v4StandardGenerator, Matrix.det_fin_two]

private lemma xiTerminalZmS3EndoscopicDeckMatrix_trace :
    xiTerminalZmS3EndoscopicDeckMatrix.trace = -1 := by
  norm_num [xiTerminalZmS3EndoscopicDeckMatrix, s4v4StandardGenerator, Matrix.trace_fin_two]

private lemma xiTerminalZmS3EndoscopicDeckMatrix_charpoly :
    xiTerminalZmS3EndoscopicDeckMatrix.charpoly = Polynomial.X ^ 2 + Polynomial.X + 1 := by
  rw [Matrix.charpoly_fin_two, xiTerminalZmS3EndoscopicDeckMatrix_trace,
    xiTerminalZmS3EndoscopicDeckMatrix_det]
  simp

/-- Paper-facing `A₂`/Coxeter package for the `S₃` endoscopic Prym block:
the polarization is the `A₂` Cartan form, hence of type `(1, 3)`, and the deck generator acts
through the order-three `A₂` Coxeter matrix.
    prop:xi-terminal-zm-s3-endoscopic-prym-a2-coxeter -/
theorem paper_xi_terminal_zm_s3_endoscopic_prym_a2_coxeter :
    xiTerminalZmS3EndoscopicPrymPolarizationIsA2 ∧
      xiTerminalZmS3EndoscopicPrymPolarizationType = (1, 3) ∧
      xiTerminalZmS3EndoscopicDeckActsByA2Coxeter := by
  refine ⟨rfl, ?_, ?_⟩
  · norm_num [xiTerminalZmS3EndoscopicPrymPolarizationType, xiTerminalZmS3EndoscopicPrymPolarization,
      a2CartanForm, Matrix.det_fin_two]
  · refine ⟨?_, xiTerminalZmS3EndoscopicDeckMatrix_trace, xiTerminalZmS3EndoscopicDeckMatrix_charpoly⟩
    native_decide

end Omega.Zeta
