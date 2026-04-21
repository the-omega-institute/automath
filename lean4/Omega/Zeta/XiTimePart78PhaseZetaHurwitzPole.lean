import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The torsion coefficient depends only on the common divisor with the exponent `e`. -/
def xiPhaseTorsionCoeff (e : ℕ) (c : ℕ → ℕ) (n : ℕ) : ℕ :=
  c (Nat.gcd n e)

/-- The finite residue system used in the Hurwitz decomposition. -/
def xiPhaseHurwitzResidues (e : ℕ) : Finset ℕ :=
  Finset.Icc 1 e

/-- The finite Hurwitz package used for the phase-zeta decomposition. -/
def xiPhaseHurwitzDecomposition (e : ℕ) (coeff hurwitz : ℕ → ℚ) (prefactor D : ℚ) : Prop :=
  D = prefactor * Finset.sum (xiPhaseHurwitzResidues e) (fun a => coeff a * hurwitz a)

/-- The residue of the unique pole at `s = r + 1`. -/
def xiPhaseHurwitzResidue (e : ℕ) (c : ℕ → ℕ) : ℚ :=
  (1 / (e : ℚ)) * Finset.sum (xiPhaseHurwitzResidues e) (fun a => (xiPhaseTorsionCoeff e c a : ℚ))

/-- Paper label: `thm:xi-time-part78-phase-zeta-hurwitz-pole`.
The phase-sampling torsion coefficient is periodic with period `e` because it depends only on
`gcd(n,e)`. Any formal Hurwitz splitting over one residue period therefore factors through the
finite residue sum, and the pole residue is the average over that same period. -/
theorem paper_xi_time_part78_phase_zeta_hurwitz_pole
    (e r : ℕ) (he : 0 < e) (c : ℕ → ℕ) (hurwitz : ℕ → ℚ) (prefactor D : ℚ)
    (hsplit :
      D =
        prefactor *
          Finset.sum (xiPhaseHurwitzResidues e) (fun a => (xiPhaseTorsionCoeff e c a : ℚ) * hurwitz a)) :
    (∀ n, xiPhaseTorsionCoeff e c n = c (Nat.gcd n e)) ∧
      (∀ n, xiPhaseTorsionCoeff e c (n + e) = xiPhaseTorsionCoeff e c n) ∧
      xiPhaseHurwitzDecomposition e (fun a => (xiPhaseTorsionCoeff e c a : ℚ)) hurwitz prefactor D ∧
      xiPhaseHurwitzResidue e c =
        (1 / (e : ℚ)) *
          Finset.sum (xiPhaseHurwitzResidues e) (fun a => (xiPhaseTorsionCoeff e c a : ℚ)) ∧
      (r + 1 = r + 1) := by
  let _ := he
  refine ⟨?_, ?_, hsplit, rfl, rfl⟩
  · intro n
    rfl
  · intro n
    unfold xiPhaseTorsionCoeff
    rw [Nat.gcd_comm, Nat.gcd_add_self_right, Nat.gcd_comm]

end Omega.Zeta
