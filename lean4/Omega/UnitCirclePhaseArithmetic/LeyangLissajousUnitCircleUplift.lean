import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

namespace Complex

/-- Local compatibility alias for the complex modulus in this mathlib snapshot. -/
noncomputable abbrev abs (z : ℂ) : ℝ := ‖z‖

end Complex

/-- Coprime phase-locked Lee--Yang/Lissajous data lifts from a single unit-circle parameter.
    prop:leyang-lissajous-unit-circle-uplift -/
theorem paper_leyang_lissajous_unit_circle_uplift
    (a b : ℕ) (δ : ℝ) (α β : ℂ) (hα : Complex.abs α = 1) (hβ : Complex.abs β = 1)
    (hrel : α ^ b = Complex.exp (((b : ℝ) * δ) * Complex.I) * β ^ a) :
    Nat.Coprime a b →
      ∃ z : ℂ, Complex.abs z = 1 ∧ α = Complex.exp (δ * Complex.I) * z ^ a ∧ β = z ^ b := by
  intro hcop
  have hαnorm : ‖α‖ = 1 := by simpa using hα
  have hβnorm : ‖β‖ = 1 := by simpa using hβ
  obtain ⟨φα, hφα⟩ := (Complex.norm_eq_one_iff α).mp hαnorm
  obtain ⟨φβ, hφβ⟩ := (Complex.norm_eq_one_iff β).mp hβnorm
  have hαpow : α ^ b = Complex.exp (((b : ℝ) * φα) * Complex.I) := by
    rw [← hφα, ← Complex.exp_nat_mul]
    simp [mul_assoc, mul_comm]
  have hβpow : β ^ a = Complex.exp (((a : ℝ) * φβ) * Complex.I) := by
    rw [← hφβ, ← Complex.exp_nat_mul]
    simp [mul_assoc, mul_comm]
  have hExp :
      Complex.exp (((b : ℝ) * φα) * Complex.I) =
        Complex.exp ((((b : ℝ) * δ) * Complex.I) + (((a : ℝ) * φβ) * Complex.I)) := by
    calc
      Complex.exp (((b : ℝ) * φα) * Complex.I) = α ^ b := hαpow.symm
      _ = Complex.exp (((b : ℝ) * δ) * Complex.I) * β ^ a := hrel
      _ = Complex.exp (((b : ℝ) * δ) * Complex.I) * Complex.exp (((a : ℝ) * φβ) * Complex.I) := by
            rw [hβpow]
      _ = Complex.exp ((((b : ℝ) * δ) * Complex.I) + (((a : ℝ) * φβ) * Complex.I)) := by
            rw [← Complex.exp_add]
  obtain ⟨k, hk⟩ := (Complex.exp_eq_exp_iff_exists_int).mp hExp
  have him :
      (b : ℝ) * φα = (b : ℝ) * δ + (a : ℝ) * φβ + (k : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hk
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_assoc,
      mul_left_comm, mul_comm] using him
  have hkReal : (b : ℝ) * (φα - δ) = (a : ℝ) * φβ + (k : ℝ) * (2 * Real.pi) := by
    linarith
  let u : ℤ := Nat.gcdA a b
  let v : ℤ := Nat.gcdB a b
  have hbez : (1 : ℤ) = a * u + b * v := by
    simpa [u, v, hcop.gcd_eq_one] using (Nat.gcd_eq_gcd_ab a b)
  have hbezReal : (1 : ℝ) = (a : ℝ) * (u : ℝ) + (b : ℝ) * (v : ℝ) := by
    exact_mod_cast hbez
  have hbezReal' : (a : ℝ) * (u : ℝ) + (b : ℝ) * (v : ℝ) = 1 := by
    linarith
  let na : ℤ := -v * k
  let nb : ℤ := u * k
  have hna : (na : ℝ) = -((v : ℝ) * (k : ℝ)) := by
    simp [na, v]
  have hnb : (nb : ℝ) = (u : ℝ) * (k : ℝ) := by
    simp [nb, u]
  let θ : ℝ := (u : ℝ) * (φα - δ) + (v : ℝ) * φβ
  have hphiβ : (a : ℝ) * φβ = (b : ℝ) * (φα - δ) - (k : ℝ) * (2 * Real.pi) := by
    linarith
  have haθ : (a : ℝ) * θ = (φα - δ) + (na : ℝ) * (2 * Real.pi) := by
    dsimp [θ]
    calc
      (a : ℝ) * ((u : ℝ) * (φα - δ) + (v : ℝ) * φβ)
          = (a : ℝ) * (u : ℝ) * (φα - δ) + (v : ℝ) * ((a : ℝ) * φβ) := by ring
      _ = (a : ℝ) * (u : ℝ) * (φα - δ) +
            (v : ℝ) * ((b : ℝ) * (φα - δ) - (k : ℝ) * (2 * Real.pi)) := by
            rw [hphiβ]
      _ = ((a : ℝ) * (u : ℝ) + (b : ℝ) * (v : ℝ)) * (φα - δ) -
            ((v : ℝ) * (k : ℝ)) * (2 * Real.pi) := by ring
      _ = (φα - δ) - ((v : ℝ) * (k : ℝ)) * (2 * Real.pi) := by
            rw [hbezReal']
            ring
      _ = (φα - δ) + (na : ℝ) * (2 * Real.pi) := by
            rw [hna]
            ring
  have hbθ : (b : ℝ) * θ = φβ + (nb : ℝ) * (2 * Real.pi) := by
    dsimp [θ]
    calc
      (b : ℝ) * ((u : ℝ) * (φα - δ) + (v : ℝ) * φβ)
          = (u : ℝ) * ((b : ℝ) * (φα - δ)) + (b : ℝ) * (v : ℝ) * φβ := by ring
      _ = (u : ℝ) * ((a : ℝ) * φβ + (k : ℝ) * (2 * Real.pi)) + (b : ℝ) * (v : ℝ) * φβ := by
            rw [hkReal]
      _ = ((a : ℝ) * (u : ℝ) + (b : ℝ) * (v : ℝ)) * φβ + ((u : ℝ) * (k : ℝ)) * (2 * Real.pi) := by
            ring
      _ = φβ + ((u : ℝ) * (k : ℝ)) * (2 * Real.pi) := by
            rw [hbezReal']
            ring
      _ = φβ + (nb : ℝ) * (2 * Real.pi) := by
            rw [hnb]
  let z : ℂ := Complex.exp (θ * Complex.I)
  have hperiodA : Complex.exp (((na : ℝ) * (2 * Real.pi)) * Complex.I) = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_int_mul_two_pi_mul_I na
  have hperiodB : Complex.exp (((nb : ℝ) * (2 * Real.pi)) * Complex.I) = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_int_mul_two_pi_mul_I nb
  have hzpowA : z ^ a = Complex.exp ((φα - δ) * Complex.I) := by
    dsimp [z]
    calc
      Complex.exp (θ * Complex.I) ^ a = Complex.exp ((a : ℕ) * (θ * Complex.I)) := by
        rw [← Complex.exp_nat_mul]
      _ = Complex.exp (((a : ℝ) * θ) * Complex.I) := by
        simp [mul_assoc, mul_comm]
      _ = Complex.exp (((φα - δ) + (na : ℝ) * (2 * Real.pi)) * Complex.I) := by
        have haθC : (((a : ℝ) * θ : ℝ) : ℂ) =
            (((φα - δ) + (na : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
          exact_mod_cast haθ
        simpa [mul_assoc, mul_comm] using congrArg (fun t : ℂ => Complex.exp (t * Complex.I)) haθC
      _ = Complex.exp (((φα - δ) * Complex.I) + (((na : ℝ) * (2 * Real.pi)) * Complex.I)) := by
        ring
      _ = Complex.exp ((φα - δ) * Complex.I) * Complex.exp (((na : ℝ) * (2 * Real.pi)) * Complex.I) := by
        rw [Complex.exp_add]
      _ = Complex.exp ((φα - δ) * Complex.I) := by
        rw [hperiodA, mul_one]
  have hzpowB : z ^ b = Complex.exp (φβ * Complex.I) := by
    dsimp [z]
    calc
      Complex.exp (θ * Complex.I) ^ b = Complex.exp ((b : ℕ) * (θ * Complex.I)) := by
        rw [← Complex.exp_nat_mul]
      _ = Complex.exp (((b : ℝ) * θ) * Complex.I) := by
        simp [mul_assoc, mul_comm]
      _ = Complex.exp ((φβ + (nb : ℝ) * (2 * Real.pi)) * Complex.I) := by
        have hbθC : (((b : ℝ) * θ : ℝ) : ℂ) =
            ((φβ + (nb : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
          exact_mod_cast hbθ
        simpa [mul_assoc, mul_comm] using congrArg (fun t : ℂ => Complex.exp (t * Complex.I)) hbθC
      _ = Complex.exp ((φβ * Complex.I) + (((nb : ℝ) * (2 * Real.pi)) * Complex.I)) := by
        ring
      _ = Complex.exp (φβ * Complex.I) * Complex.exp (((nb : ℝ) * (2 * Real.pi)) * Complex.I) := by
        rw [Complex.exp_add]
      _ = Complex.exp (φβ * Complex.I) := by
        rw [hperiodB, mul_one]
  refine ⟨z, ?_, ?_, ?_⟩
  · dsimp [z]
    simpa using Complex.norm_exp_ofReal_mul_I θ
  · calc
      α = Complex.exp (φα * Complex.I) := hφα.symm
      _ = Complex.exp (δ * Complex.I) * Complex.exp ((φα - δ) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            ring
      _ = Complex.exp (δ * Complex.I) * z ^ a := by
            rw [hzpowA.symm]
  · calc
      β = Complex.exp (φβ * Complex.I) := hφβ.symm
      _ = z ^ b := hzpowB.symm

end Omega.UnitCirclePhaseArithmetic
