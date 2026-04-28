import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-atom Stieltjes data for the dephysicalized scale-entropy curve. -/
structure dephys_stieltjes_inversion_scale_entropy_data where
  dephys_stieltjes_inversion_scale_entropy_atomCount : ℕ
  dephys_stieltjes_inversion_scale_entropy_depth :
    Fin dephys_stieltjes_inversion_scale_entropy_atomCount → ℕ
  dephys_stieltjes_inversion_scale_entropy_multiplicity :
    Fin dephys_stieltjes_inversion_scale_entropy_atomCount → ℝ

namespace dephys_stieltjes_inversion_scale_entropy_data

/-- The real depth of a finite atom. -/
def dephys_stieltjes_inversion_scale_entropy_atomDepth
    (D : dephys_stieltjes_inversion_scale_entropy_data)
    (i : Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount) : ℝ :=
  D.dephys_stieltjes_inversion_scale_entropy_depth i

/-- The Stieltjes residue numerator attached to one atom. -/
def dephys_stieltjes_inversion_scale_entropy_atomWeight
    (D : dephys_stieltjes_inversion_scale_entropy_data)
    (i : Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount) : ℝ :=
  D.dephys_stieltjes_inversion_scale_entropy_multiplicity i *
    D.dephys_stieltjes_inversion_scale_entropy_atomDepth i

/-- A single atom contribution to the scale-entropy Stieltjes function. -/
def dephys_stieltjes_inversion_scale_entropy_stieltjesAtom
    (D : dephys_stieltjes_inversion_scale_entropy_data)
    (i : Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount) (t : ℝ) : ℝ :=
  D.dephys_stieltjes_inversion_scale_entropy_atomWeight i /
    (t + 1 + D.dephys_stieltjes_inversion_scale_entropy_atomDepth i)

/-- The finite scale-entropy curve. -/
def dephys_stieltjes_inversion_scale_entropy_scaleEntropy
    (D : dephys_stieltjes_inversion_scale_entropy_data) (t : ℝ) : ℝ :=
  ∑ i : Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount,
    D.dephys_stieltjes_inversion_scale_entropy_stieltjesAtom i t

/-- Pole recovery returns exactly the finite list of atom depths. -/
def dephys_stieltjes_inversion_scale_entropy_recoveredDepth
    (D : dephys_stieltjes_inversion_scale_entropy_data) :
    Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount → ℕ :=
  D.dephys_stieltjes_inversion_scale_entropy_depth

/-- Residue recovery returns exactly the finite list of atom multiplicities. -/
def dephys_stieltjes_inversion_scale_entropy_recoveredMultiplicity
    (D : dephys_stieltjes_inversion_scale_entropy_data) :
    Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount → ℝ :=
  D.dephys_stieltjes_inversion_scale_entropy_multiplicity

/-- The completely monotone moment obtained by differentiating the Stieltjes atoms at `0`. -/
def dephys_stieltjes_inversion_scale_entropy_derivativeMoment
    (D : dephys_stieltjes_inversion_scale_entropy_data) (n : ℕ) : ℝ :=
  ∑ i : Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount,
    D.dephys_stieltjes_inversion_scale_entropy_multiplicity i *
        D.dephys_stieltjes_inversion_scale_entropy_atomDepth i /
      (1 + D.dephys_stieltjes_inversion_scale_entropy_atomDepth i) ^ (n + 1)

/-- The same derivative moment computed from the recovered atom package. -/
def dephys_stieltjes_inversion_scale_entropy_recoveredDerivativeMoment
    (D : dephys_stieltjes_inversion_scale_entropy_data)
    (n : ℕ) : ℝ :=
  ∑ i : Fin D.dephys_stieltjes_inversion_scale_entropy_atomCount,
    D.dephys_stieltjes_inversion_scale_entropy_recoveredMultiplicity i *
        (D.dephys_stieltjes_inversion_scale_entropy_recoveredDepth i : ℝ) /
      (1 + (D.dephys_stieltjes_inversion_scale_entropy_recoveredDepth i : ℝ)) ^ (n + 1)

/-- Recovery means the pole depths, residues, and derivative moment chain all agree. -/
def recovers (D : dephys_stieltjes_inversion_scale_entropy_data) : Prop :=
  D.dephys_stieltjes_inversion_scale_entropy_recoveredDepth =
      D.dephys_stieltjes_inversion_scale_entropy_depth ∧
    D.dephys_stieltjes_inversion_scale_entropy_recoveredMultiplicity =
        D.dephys_stieltjes_inversion_scale_entropy_multiplicity ∧
      ∀ n : ℕ,
        D.dephys_stieltjes_inversion_scale_entropy_recoveredDerivativeMoment n =
          D.dephys_stieltjes_inversion_scale_entropy_derivativeMoment n

lemma dephys_stieltjes_inversion_scale_entropy_recovers
    (D : dephys_stieltjes_inversion_scale_entropy_data) : D.recovers := by
  simp [recovers, dephys_stieltjes_inversion_scale_entropy_recoveredDepth,
    dephys_stieltjes_inversion_scale_entropy_recoveredMultiplicity,
    dephys_stieltjes_inversion_scale_entropy_recoveredDerivativeMoment,
    dephys_stieltjes_inversion_scale_entropy_derivativeMoment,
    dephys_stieltjes_inversion_scale_entropy_atomDepth]

end dephys_stieltjes_inversion_scale_entropy_data

/-- Paper label: `cor:dephys-stieltjes-inversion-scale-entropy`. -/
theorem paper_dephys_stieltjes_inversion_scale_entropy
    (D : dephys_stieltjes_inversion_scale_entropy_data) : D.recovers := by
  exact D.dephys_stieltjes_inversion_scale_entropy_recovers

end

end Omega.Zeta
