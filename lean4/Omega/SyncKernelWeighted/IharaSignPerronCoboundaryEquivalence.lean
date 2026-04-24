import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.SyncKernelWeighted.IharaArtinFactorization

namespace Omega.SyncKernelWeighted

open Matrix

/-- The primitive trivial Hashimoto block for the directed `3`-cycle. -/
def primitiveTrivialHashimotoBlock : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
    0, 0, 1;
    1, 0, 0]

/-- The same primitive block with a sign twist on each directed edge. -/
def primitiveSignTwistedHashimotoBlock (a b c : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, a, 0;
    0, 0, b;
    c, 0, 0]

/-- Diagonal gauge matrices with vertex signs. -/
def primitiveSignGauge (σ₀ σ₁ σ₂ : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![σ₀, 0, 0;
    0, σ₁, 0;
    0, 0, σ₂]

/-- The sign twist is a coboundary on the primitive component if it is obtained by diagonal
conjugacy from the trivial block. -/
def primitiveCoboundaryWitness (a b c : ℤ) : Prop :=
  ∃ σ₀ σ₁ σ₂ : ℤ,
    σ₀ ^ 2 = 1 ∧ σ₁ ^ 2 = 1 ∧ σ₂ ^ 2 = 1 ∧
      primitiveSignTwistedHashimotoBlock a b c =
        primitiveSignGauge σ₀ σ₁ σ₂ *
          primitiveTrivialHashimotoBlock *
          primitiveSignGauge σ₀ σ₁ σ₂

/-- The twisted primitive block still has the same Perron point `1` as the trivial block. -/
def primitiveHasPerronPoint (a b c : ℤ) : Prop :=
  Matrix.det (1 - primitiveSignTwistedHashimotoBlock a b c) = 0

lemma primitiveSignGauge_conjugation (σ₀ σ₁ σ₂ : ℤ) :
    primitiveSignGauge σ₀ σ₁ σ₂ * primitiveTrivialHashimotoBlock *
        primitiveSignGauge σ₀ σ₁ σ₂ =
      primitiveSignTwistedHashimotoBlock (σ₀ * σ₁) (σ₁ * σ₂) (σ₂ * σ₀) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primitiveSignGauge, primitiveTrivialHashimotoBlock,
      primitiveSignTwistedHashimotoBlock, Matrix.mul_apply, Fin.sum_univ_three]

lemma det_one_sub_primitiveSignTwistedHashimotoBlock (a b c : ℤ) :
    Matrix.det (1 - primitiveSignTwistedHashimotoBlock a b c) = 1 - a * b * c := by
  simp [primitiveSignTwistedHashimotoBlock, Matrix.det_fin_three]
  ring

lemma primitiveHasPerronPoint_iff_cycleProduct (a b c : ℤ) :
    primitiveHasPerronPoint a b c ↔ a * b * c = 1 := by
  unfold primitiveHasPerronPoint
  rw [det_one_sub_primitiveSignTwistedHashimotoBlock]
  constructor <;> intro h <;> linarith

lemma primitiveCoboundaryWitness_of_cycleProduct (a b c : ℤ)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hprod : a * b * c = 1) :
    primitiveCoboundaryWitness a b c := by
  have hab : (a * b) ^ 2 = 1 := by
    calc
      (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
      _ = 1 := by rw [ha, hb]; norm_num
  have hc' : c = a * b := by
    calc
      c = c * 1 := by ring
      _ = c * (a * b * c) := by rw [hprod]
      _ = (c ^ 2) * (a * b) := by ring
      _ = a * b := by rw [hc]; ring
  have hb' : a * (a * b) = b := by
    calc
      a * (a * b) = a ^ 2 * b := by ring
      _ = b := by rw [ha]; ring
  refine ⟨1, a, a * b, by norm_num, ha, hab, ?_⟩
  simpa [hc', hb'] using (primitiveSignGauge_conjugation 1 a (a * b)).symm

lemma cycleProduct_of_primitiveCoboundaryWitness (a b c : ℤ)
    (hw : primitiveCoboundaryWitness a b c) : a * b * c = 1 := by
  rcases hw with ⟨σ₀, σ₁, σ₂, hσ₀, hσ₁, hσ₂, hw⟩
  rw [primitiveSignGauge_conjugation] at hw
  have ha : a = σ₀ * σ₁ := by
    have hentry := congrArg (fun M => M 0 1) hw
    simpa [primitiveSignTwistedHashimotoBlock] using hentry
  have hb : b = σ₁ * σ₂ := by
    have hentry := congrArg (fun M => M 1 2) hw
    simpa [primitiveSignTwistedHashimotoBlock] using hentry
  have hc : c = σ₂ * σ₀ := by
    have hentry := congrArg (fun M => M 2 0) hw
    simpa [primitiveSignTwistedHashimotoBlock] using hentry
  calc
    a * b * c = (σ₀ * σ₁) * (σ₁ * σ₂) * (σ₂ * σ₀) := by rw [ha, hb, hc]
    _ = σ₀ ^ 2 * σ₁ ^ 2 * σ₂ ^ 2 := by ring
    _ = 1 := by rw [hσ₀, hσ₁, hσ₂]; ring

/-- Paper label: `cor:ihara-sgn-perron-coboundary-equivalence`.
For the primitive `3`-cycle block with edge signs in `{±1}`, the sign twist is a coboundary
exactly when the twisted block retains the Perron point `1` of the trivial Hashimoto block. -/
theorem paper_ihara_sgn_perron_coboundary_equivalence (a b c : ℤ)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) :
    primitiveCoboundaryWitness a b c ↔ primitiveHasPerronPoint a b c := by
  rw [primitiveHasPerronPoint_iff_cycleProduct]
  constructor
  · exact cycleProduct_of_primitiveCoboundaryWitness a b c
  · exact primitiveCoboundaryWitness_of_cycleProduct a b c ha hb hc

end Omega.SyncKernelWeighted
