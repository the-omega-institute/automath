import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- The cyclic quotient size `|Gₘ| = F_{m+2}`. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_period (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The basic root of unity sampled at frequency `k`. -/
noncomputable def conclusion_zeckendorf_euler_wrapped_poisson_fourier_root
    (m : ℕ) (k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) : ℂ :=
  Complex.exp
    (-(((2 : ℝ) * Real.pi * (k : ℕ)) /
        (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m : ℝ)) * Complex.I)

/-- The character `χₖ(r) = ωₖ^r` on the finite cyclic quotient. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_character
    (m : ℕ)
    (k r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) : ℂ :=
  conclusion_zeckendorf_euler_wrapped_poisson_fourier_root m k ^ r.1

/-- The finite truncated exponential `E_F(t) = ∑_{n=0}^{F-1} t^n / n!`, written with factorial
inverses. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_truncated_exponential
    (m : ℕ) (t : ℂ) : ℂ :=
  ∑ r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
    ((Nat.factorial r.1 : ℂ)⁻¹) * t ^ r.1

/-- The canonical Euler packet on the cyclic quotient. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_packet
    (m : ℕ) (t : ℂ)
    (r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) : ℂ :=
  (conclusion_zeckendorf_euler_wrapped_poisson_fourier_truncated_exponential m t)⁻¹ *
    ((Nat.factorial r.1 : ℂ)⁻¹) * t ^ r.1

/-- The Fourier transform of the Euler packet. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_fourier
    (m : ℕ) (t : ℂ)
    (k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) : ℂ :=
  ∑ r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
    conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_packet m t r *
      conclusion_zeckendorf_euler_wrapped_poisson_fourier_character m k r

/-- The twisted truncated exponential `E_F(t ωₖ)`. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_twisted_truncated_exponential
    (m : ℕ) (t : ℂ)
    (k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) : ℂ :=
  ∑ r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
    ((Nat.factorial r.1 : ℂ)⁻¹) *
      (t * conclusion_zeckendorf_euler_wrapped_poisson_fourier_root m k) ^ r.1

/-- The wrapped Poisson Fourier symbol. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_wrapped_poisson_fourier
    (m : ℕ) (t : ℂ)
    (k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) : ℂ :=
  Complex.exp (t * (conclusion_zeckendorf_euler_wrapped_poisson_fourier_root m k - 1))

/-- A spatial wrapped Poisson kernel obtained by inverse finite Fourier synthesis from the closed
symbol. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_wrapped_poisson_kernel
    (m : ℕ) (t : ℂ)
    (r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m)) : ℂ :=
  ((conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m : ℂ)⁻¹) *
    ∑ k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
      conclusion_zeckendorf_euler_wrapped_poisson_fourier_wrapped_poisson_fourier m t k *
        (conclusion_zeckendorf_euler_wrapped_poisson_fourier_character m k r)⁻¹

/-- Conclusion package for the finite-resolution Euler/wrapped-Poisson Fourier symbols. -/
def conclusion_zeckendorf_euler_wrapped_poisson_fourier_statement (m : Nat) : Prop :=
  ∀ t : ℂ,
    (∀ k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
      conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_fourier m t k =
        (conclusion_zeckendorf_euler_wrapped_poisson_fourier_truncated_exponential m t)⁻¹ *
          conclusion_zeckendorf_euler_wrapped_poisson_fourier_twisted_truncated_exponential
            m t k) ∧
    (∀ k : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
      conclusion_zeckendorf_euler_wrapped_poisson_fourier_wrapped_poisson_fourier m t k =
        Complex.exp (t * (conclusion_zeckendorf_euler_wrapped_poisson_fourier_root m k - 1)))

/-- Paper label: `thm:conclusion-zeckendorf-euler-wrapped-poisson-fourier`. -/
theorem paper_conclusion_zeckendorf_euler_wrapped_poisson_fourier (m : Nat) :
    conclusion_zeckendorf_euler_wrapped_poisson_fourier_statement m := by
  intro t
  refine ⟨?_, ?_⟩
  · intro k
    calc
      conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_fourier m t k
          =
            ∑ r : Fin (conclusion_zeckendorf_euler_wrapped_poisson_fourier_period m),
              (conclusion_zeckendorf_euler_wrapped_poisson_fourier_truncated_exponential m t)⁻¹ *
                (((Nat.factorial r.1 : ℂ)⁻¹) *
                  (t * conclusion_zeckendorf_euler_wrapped_poisson_fourier_root m k) ^ r.1) := by
              unfold conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_fourier
                conclusion_zeckendorf_euler_wrapped_poisson_fourier_euler_packet
                conclusion_zeckendorf_euler_wrapped_poisson_fourier_character
              refine Finset.sum_congr rfl ?_
              intro r hr
              simp [mul_assoc, mul_left_comm, mul_comm, mul_pow]
      _ =
          (conclusion_zeckendorf_euler_wrapped_poisson_fourier_truncated_exponential m t)⁻¹ *
            conclusion_zeckendorf_euler_wrapped_poisson_fourier_twisted_truncated_exponential
              m t k := by
            rw [← Finset.mul_sum]
            rfl
  · intro k
    rfl

end

end Omega.Conclusion
