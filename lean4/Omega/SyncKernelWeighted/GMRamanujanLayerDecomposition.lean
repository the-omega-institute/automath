import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Concrete finite Fourier-kernel parameters for the denominator layer. -/
structure gm_ramanujan_layer_decomposition_data where
  gm_ramanujan_layer_decomposition_modulus : ℕ
  gm_ramanujan_layer_decomposition_frequency : ℕ

/-- Primitive residue representatives modulo `q`, written inside `Finset.range q`. -/
def gm_ramanujan_layer_decomposition_primitiveResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a => Nat.Coprime a q

/-- The finite Fourier phase used by the denominator layer. -/
noncomputable def gm_ramanujan_layer_decomposition_phase
    (q n a : ℕ) : ℂ :=
  Complex.exp
    (2 * Real.pi * Complex.I * (((a * n : ℕ) : ℝ) / (q : ℝ)))

/-- Fourier coefficient for the primitive denominator layer. -/
noncomputable def gm_ramanujan_layer_decomposition_fourierCoeff
    (q a : ℕ) : ℂ :=
  if Nat.Coprime a q then 1 else 0

/-- The denominator-layer specialization of the finite Fourier kernel. -/
noncomputable def gm_ramanujan_layer_decomposition_denominatorLayer
    (q n : ℕ) : ℂ :=
  (Finset.range q).sum fun a =>
    gm_ramanujan_layer_decomposition_fourierCoeff q a *
      gm_ramanujan_layer_decomposition_phase q n a

/-- The Ramanujan sum over primitive residues. -/
noncomputable def gm_ramanujan_layer_decomposition_ramanujanSum
    (q n : ℕ) : ℂ :=
  (gm_ramanujan_layer_decomposition_primitiveResidues q).sum fun a =>
    gm_ramanujan_layer_decomposition_phase q n a

/-- The finite Fourier-kernel layer reduces to the Ramanujan sum. -/
def gm_ramanujan_layer_decomposition_statement
    (D : gm_ramanujan_layer_decomposition_data) : Prop :=
  gm_ramanujan_layer_decomposition_denominatorLayer
      D.gm_ramanujan_layer_decomposition_modulus
      D.gm_ramanujan_layer_decomposition_frequency =
    gm_ramanujan_layer_decomposition_ramanujanSum
      D.gm_ramanujan_layer_decomposition_modulus
      D.gm_ramanujan_layer_decomposition_frequency

/-- Paper label: `prop:gm-ramanujan-layer-decomposition`. -/
theorem paper_gm_ramanujan_layer_decomposition
    (D : gm_ramanujan_layer_decomposition_data) :
    gm_ramanujan_layer_decomposition_statement D := by
  classical
  unfold gm_ramanujan_layer_decomposition_statement
    gm_ramanujan_layer_decomposition_denominatorLayer
    gm_ramanujan_layer_decomposition_ramanujanSum
    gm_ramanujan_layer_decomposition_primitiveResidues
    gm_ramanujan_layer_decomposition_fourierCoeff
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro a _
  by_cases h : Nat.Coprime a D.gm_ramanujan_layer_decomposition_modulus
  · simp
  · simp [h]

end Omega.SyncKernelWeighted
