import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial

/-- The polynomial-level Chebyshev-Adams lift used in the Frobenius congruence package. -/
noncomputable def chebyAdamsPoly (p : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ p

lemma chebyAdamsPoly_eq_expand_X (p : ℕ) :
    chebyAdamsPoly p = Polynomial.expand ℤ p Polynomial.X := by
  simp [chebyAdamsPoly]

lemma coeff_comp_chebyAdams_sub_pow_dvd
    (p : ℕ) (hp : Nat.Prime p) (f : Polynomial ℤ) (n : ℕ) :
    ((p : ℤ) ∣ (f.comp (chebyAdamsPoly p) - f ^ p).coeff n) := by
  letI : Fact p.Prime := ⟨hp⟩
  let fmod : Polynomial (ZMod p) := f.map (Int.castRingHom (ZMod p))
  have hExpandEqPow : Polynomial.expand (ZMod p) p fmod = fmod ^ p := by
    calc
      Polynomial.expand (ZMod p) p fmod =
          Polynomial.map (frobenius (ZMod p) p) (Polynomial.expand (ZMod p) p fmod) := by
            ext k
            simp
      _ = fmod ^ p := Polynomial.map_frobenius_expand (R := ZMod p) (p := p) fmod
  have hMapZero :
      Polynomial.map (Int.castRingHom (ZMod p)) (f.comp (chebyAdamsPoly p) - f ^ p) = 0 := by
    calc
      Polynomial.map (Int.castRingHom (ZMod p)) (f.comp (chebyAdamsPoly p) - f ^ p)
          = Polynomial.map (Int.castRingHom (ZMod p)) (f.comp (chebyAdamsPoly p)) -
              Polynomial.map (Int.castRingHom (ZMod p)) (f ^ p) := by
              rw [Polynomial.map_sub]
      _ = Polynomial.expand (ZMod p) p fmod - fmod ^ p := by
            rw [Polynomial.map_comp]
            simp [fmod, chebyAdamsPoly, Polynomial.expand_eq_comp_X_pow]
      _ = 0 := by rw [hExpandEqPow, sub_self]
  have hCoeffPow : (fmod ^ p).coeff n = (((f ^ p).coeff n : ℤ) : ZMod p) := by
    simpa [fmod] using
      (Polynomial.coeff_map (f := Int.castRingHom (ZMod p)) (p := f ^ p) n)
  have hCoeffRaw :
      (((f.comp (chebyAdamsPoly p)).coeff n : ℤ) : ZMod p) - (fmod ^ p).coeff n = 0 := by
    have := congrArg (fun q : Polynomial (ZMod p) => q.coeff n) hMapZero
    simpa [Polynomial.coeff_map, Polynomial.coeff_sub, fmod] using this
  have hCoeffZero' :
      (((f.comp (chebyAdamsPoly p) - f ^ p).coeff n : ℤ) : ZMod p) = 0 := by
    calc
      (((f.comp (chebyAdamsPoly p) - f ^ p).coeff n : ℤ) : ZMod p)
          = (((f.comp (chebyAdamsPoly p)).coeff n : ℤ) : ZMod p) -
              (((f ^ p).coeff n : ℤ) : ZMod p) := by
              simp [Polynomial.coeff_sub]
      _ = (((f.comp (chebyAdamsPoly p)).coeff n : ℤ) : ZMod p) - (fmod ^ p).coeff n := by
            rw [hCoeffPow]
      _ = 0 := hCoeffRaw
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hCoeffZero'

/-- Paper label: `prop:chebyshev-frobenius-pderivation-integrality`.
Composing with the Adams lift differs from Frobenius by a polynomial multiple of `p`. -/
theorem paper_chebyshev_frobenius_pderivation_integrality
    (p : ℕ) (hp : Nat.Prime p) (f : Polynomial ℤ) :
    ∃ δ : Polynomial ℤ, f.comp (chebyAdamsPoly p) = f ^ p + Polynomial.C (p : ℤ) * δ := by
  let defect : Polynomial ℤ := f.comp (chebyAdamsPoly p) - f ^ p
  have hdvd : Polynomial.C (p : ℤ) ∣ defect := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    simpa [defect] using coeff_comp_chebyAdams_sub_pow_dvd p hp f n
  rcases hdvd with ⟨δ, hδ⟩
  refine ⟨δ, ?_⟩
  calc
    f.comp (chebyAdamsPoly p) = f ^ p + defect := by
      simp [defect]
    _ = f ^ p + Polynomial.C (p : ℤ) * δ := by rw [hδ]

end Omega.SyncKernelWeighted
