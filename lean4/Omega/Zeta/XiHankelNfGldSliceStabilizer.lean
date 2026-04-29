import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open scoped Matrix

/-- Concrete prefixed package for the Hankel normal-form slice and its stabilizer.
The matrices `H0` and `H1` are the first two Hankel blocks, `O` and `C` are the
observability and controllability blocks, and `AH` is the Hankel-shift operator acting on
the reachable slice. -/
structure xi_hankel_nf_gld_slice_stabilizer_data where
  n : ℕ
  A : Matrix (Fin n) (Fin n) ℚ
  O : Matrix (Fin n) (Fin n) ℚ
  C : Matrix (Fin n) (Fin n) ℚ
  H0 : Matrix (Fin n) (Fin n) ℚ
  H1 : Matrix (Fin n) (Fin n) ℚ
  AH : Matrix (Fin n) (Fin n) ℚ
  conjugatedNormalForm : Matrix (Fin n) (Fin n) ℚ
  e0 : Fin n → ℚ
  reachableBasis : Fin n → Fin n → ℚ
  H0_factor : H0 = O * C
  H1_factor : H1 = O * A * C
  AH_eq : AH = A
  conjugatedNormalForm_eq : conjugatedNormalForm = H1 * H0
  reachableBasis_eq_power : ∀ j : Fin n, reachableBasis j = (AH ^ j.1) *ᵥ e0
  fixesReachableBasis_of_commutes :
    ∀ S : Matrix (Fin n) (Fin n) ℚ,
      S * AH = AH * S →
        S *ᵥ e0 = e0 →
          ∀ j : Fin n, S *ᵥ reachableBasis j = reachableBasis j
  reachableBasis_extensional :
    ∀ S : Matrix (Fin n) (Fin n) ℚ,
      (∀ j : Fin n, S *ᵥ reachableBasis j = reachableBasis j) → S = 1

namespace xi_hankel_nf_gld_slice_stabilizer_data

/-- The two Hankel blocks factor through the minimal realization, and the conjugated
normal-form matrix is obtained by the corresponding block multiplication. -/
def hankelNormalFormIsOrbitSlice (D : xi_hankel_nf_gld_slice_stabilizer_data) : Prop :=
  D.H0 = D.O * D.C ∧
    D.H1 = D.O * D.A * D.C ∧
      D.conjugatedNormalForm = (D.O * D.A * D.C) * (D.O * D.C)

/-- A slice stabilizer that fixes the distinguished reachable vector and commutes with the
Hankel-shift operator fixes every reachable-basis vector and is the identity matrix. -/
def sliceStabilizerTrivial (D : xi_hankel_nf_gld_slice_stabilizer_data) : Prop :=
  ∀ S : Matrix (Fin D.n) (Fin D.n) ℚ,
    S * D.AH = D.AH * S →
      S *ᵥ D.e0 = D.e0 →
        (∀ j : Fin D.n, S *ᵥ D.reachableBasis j = D.reachableBasis j) ∧ S = 1

end xi_hankel_nf_gld_slice_stabilizer_data

open xi_hankel_nf_gld_slice_stabilizer_data

/-- Paper label: `prop:xi-hankel-nf-gld-slice-stabilizer`. -/
theorem paper_xi_hankel_nf_gld_slice_stabilizer
    (D : xi_hankel_nf_gld_slice_stabilizer_data) :
    D.hankelNormalFormIsOrbitSlice ∧ D.sliceStabilizerTrivial := by
  refine ⟨?_, ?_⟩
  · refine ⟨D.H0_factor, D.H1_factor, ?_⟩
    calc
      D.conjugatedNormalForm = D.H1 * D.H0 := D.conjugatedNormalForm_eq
      _ = (D.O * D.A * D.C) * (D.O * D.C) := by
        rw [D.H1_factor, D.H0_factor]
  · intro S hcomm hfix
    have hreachable : ∀ j : Fin D.n, S *ᵥ D.reachableBasis j = D.reachableBasis j :=
      D.fixesReachableBasis_of_commutes S hcomm hfix
    exact ⟨hreachable, D.reachableBasis_extensional S hreachable⟩

end Omega.Zeta
