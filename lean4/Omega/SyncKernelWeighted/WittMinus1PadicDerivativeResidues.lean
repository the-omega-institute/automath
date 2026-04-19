import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittFrobeniusDefectDivisibility

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Concrete data for the `u = -1` `p`-adic derivative residue package. The stage polynomials model
the Witt lifts, `residue k` is the derivative residue read at level `k`, and the Euler-derivative
identity identifies consecutive residue differences with a fixed coefficient of the Frobenius
defect polynomial. -/
structure WittMinus1PadicDerivativeResiduesData where
  p : ℕ
  hp : Nat.Prime p
  r : ℕ
  stage : ℕ → Polynomial ℤ
  residue : ℕ → ℤ
  residueIndex : ℕ
  coeffCongruence :
    ∀ k, r + 1 ≤ k →
      ∀ j, ((p ^ (k - r) : ℤ) ∣ (stage k).coeff j - if p ∣ j then (stage (k - 1)).coeff (j / p) else 0)
  eulerDerivativeIdentity :
    ∀ k, r + 1 ≤ k →
      residue k - residue (k - 1) =
        (wittFrobeniusDefect p (stage k) (stage (k - 1))).coeff residueIndex

namespace WittMinus1PadicDerivativeResiduesData

/-- Successive derivative residues become divisible by progressively higher powers of `p`
once the Frobenius defect is read through the Euler-derivative identity. -/
def divisibilityClaim (D : WittMinus1PadicDerivativeResiduesData) : Prop :=
  ∀ k, D.r + 1 ≤ k → ((D.p ^ (k - D.r) : ℤ) ∣ D.residue k - D.residue (k - 1))

/-- All derivative residues stabilize modulo `p` after the base level `r + 1`. -/
def modPStabilityClaim (D : WittMinus1PadicDerivativeResiduesData) : Prop :=
  ∀ k, D.r + 1 ≤ k → ((D.residue k : ZMod D.p) = D.residue (D.r + 1))

/-- The derivative residues form a `p`-adic Cauchy sequence in the sense that later differences are
divisible by the power attached to the earlier level. -/
def zpCauchyClaim (D : WittMinus1PadicDerivativeResiduesData) : Prop :=
  ∀ k ell, D.r + 1 ≤ k → k ≤ ell → ((D.p ^ (k - D.r) : ℤ) ∣ D.residue ell - D.residue k)

end WittMinus1PadicDerivativeResiduesData

open WittMinus1PadicDerivativeResiduesData

/-- The Frobenius defect divisibility theorem supplies the base seed at level `r + 1`; iterating
the same coefficientwise divisibility along the residue-difference identity makes the residue
sequence stable modulo `p` and Cauchy in `ℤ_p`.
    cor:witt-minus1-padic-derivative-residues -/
theorem paper_witt_minus1_padic_derivative_residues
    (D : WittMinus1PadicDerivativeResiduesData) :
    D.divisibilityClaim ∧ D.modPStabilityClaim ∧ D.zpCauchyClaim := by
  have hdiv :
      ∀ k, D.r + 1 ≤ k → ((D.p ^ (k - D.r) : ℤ) ∣ D.residue k - D.residue (k - 1)) := by
    intro k hk
    have hk' : 1 ≤ k - D.r := by omega
    have hdef :=
      paper_witt_frobenius_defect_divisibility
        D.p (k - D.r) D.hp hk' (D.stage k) (D.stage (k - 1)) (D.coeffCongruence k hk)
    simpa [D.eulerDerivativeIdentity k hk] using hdef D.residueIndex
  have hseed : ((D.p : ℤ) ∣ D.residue (D.r + 1) - D.residue D.r) := by
    simpa using hdiv (D.r + 1) (le_rfl : D.r + 1 ≤ D.r + 1)
  have hcauchy :
      ∀ k ell, D.r + 1 ≤ k → k ≤ ell → ((D.p ^ (k - D.r) : ℤ) ∣ D.residue ell - D.residue k) := by
    intro k ell hk hkell
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkell
    induction n with
    | zero =>
        simpa using (dvd_zero (D.p ^ (k - D.r) : ℤ))
    | succ n ih =>
        have hstepStrong :
            ((D.p ^ ((k + n + 1) - D.r) : ℤ) ∣
              D.residue (k + n + 1) - D.residue (k + n)) := by
          exact hdiv (k + n + 1) (by omega)
        have hpowNat : D.p ^ (k - D.r) ∣ D.p ^ ((k + n + 1) - D.r) := by
          exact pow_dvd_pow D.p (by omega)
        have hpowInt : ((D.p ^ (k - D.r) : ℤ) ∣ (D.p ^ ((k + n + 1) - D.r) : ℤ)) := by
          rcases hpowNat with ⟨t, ht⟩
          refine ⟨(t : ℤ), ?_⟩
          exact_mod_cast ht
        have hstepWeak :
            ((D.p ^ (k - D.r) : ℤ) ∣ D.residue (k + n + 1) - D.residue (k + n)) :=
          dvd_trans hpowInt hstepStrong
        have hsplit :
            D.residue (k + n + 1) - D.residue k =
              (D.residue (k + n + 1) - D.residue (k + n)) +
                (D.residue (k + n) - D.residue k) := by
          ring
        simpa [Nat.add_assoc, hsplit] using Int.dvd_add hstepWeak (ih (by omega))
  refine ⟨hdiv, ?_, hcauchy⟩
  intro k hk
  have hdiff : ((D.p : ℤ) ∣ D.residue k - D.residue (D.r + 1)) := by
    simpa using hcauchy (D.r + 1) k (le_rfl : D.r + 1 ≤ D.r + 1) hk
  have hz : (((D.residue k - D.residue (D.r + 1) : ℤ) : ZMod D.p)) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdiff
  have hsub : ((D.residue k : ZMod D.p) - D.residue (D.r + 1)) = 0 := by
    simpa using hz
  exact sub_eq_zero.mp hsub

end Omega.SyncKernelWeighted
