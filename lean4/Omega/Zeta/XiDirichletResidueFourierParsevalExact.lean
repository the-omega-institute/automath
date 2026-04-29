import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete cyclic modulus `2`, used as the smallest exact Fourier/Parseval residue model. -/
abbrev xi_dirichlet_residue_fourier_parseval_exact_modulus := Fin 2

/-- The order-two character on the concrete residue group. -/
def xi_dirichlet_residue_fourier_parseval_exact_character
    (j r : xi_dirichlet_residue_fourier_parseval_exact_modulus) : ℂ :=
  if j = 0 ∨ r = 0 then 1 else -1

/-- Twisted trace of a residue-count function against the order-two characters. -/
def xi_dirichlet_residue_fourier_parseval_exact_trace
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ)
    (j : xi_dirichlet_residue_fourier_parseval_exact_modulus) : ℂ :=
  ∑ r, counts r * xi_dirichlet_residue_fourier_parseval_exact_character j r

/-- Mean residue count. -/
def xi_dirichlet_residue_fourier_parseval_exact_mean
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) : ℂ :=
  (∑ r, counts r) / 2

/-- Centered residue-count sequence. -/
def xi_dirichlet_residue_fourier_parseval_exact_centered
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ)
    (r : xi_dirichlet_residue_fourier_parseval_exact_modulus) : ℂ :=
  counts r - xi_dirichlet_residue_fourier_parseval_exact_mean counts

/-- Parseval energy of the centered residue-count sequence. -/
def xi_dirichlet_residue_fourier_parseval_exact_centeredEnergy
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) : ℝ :=
  ∑ r, Complex.normSq (xi_dirichlet_residue_fourier_parseval_exact_centered counts r)

/-- Energy of the unique nonzero Fourier mode. -/
def xi_dirichlet_residue_fourier_parseval_exact_nonzeroEnergy
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Complex.normSq (xi_dirichlet_residue_fourier_parseval_exact_trace counts 1)

private lemma xi_dirichlet_residue_fourier_parseval_exact_sum_modulus {R : Type*}
    [AddCommMonoid R] (f : xi_dirichlet_residue_fourier_parseval_exact_modulus → R) :
    (∑ x, f x) = f 0 + f 1 := by
  have huniv :
      (Finset.univ : Finset xi_dirichlet_residue_fourier_parseval_exact_modulus) = {0, 1} := by
    native_decide
  rw [huniv]
  simp

private theorem xi_dirichlet_residue_fourier_parseval_exact_trace_zero
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) :
    xi_dirichlet_residue_fourier_parseval_exact_trace counts 0 = counts 0 + counts 1 := by
  rw [xi_dirichlet_residue_fourier_parseval_exact_trace,
    xi_dirichlet_residue_fourier_parseval_exact_sum_modulus]
  norm_num [xi_dirichlet_residue_fourier_parseval_exact_character]

private theorem xi_dirichlet_residue_fourier_parseval_exact_trace_one
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) :
    xi_dirichlet_residue_fourier_parseval_exact_trace counts 1 = counts 0 - counts 1 := by
  rw [xi_dirichlet_residue_fourier_parseval_exact_trace,
    xi_dirichlet_residue_fourier_parseval_exact_sum_modulus]
  simp [xi_dirichlet_residue_fourier_parseval_exact_character]
  ring

private theorem xi_dirichlet_residue_fourier_parseval_exact_inversion
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) :
    ∀ r : xi_dirichlet_residue_fourier_parseval_exact_modulus,
      counts r =
        (1 / (2 : ℂ)) *
          ∑ j, xi_dirichlet_residue_fourier_parseval_exact_trace counts j *
            xi_dirichlet_residue_fourier_parseval_exact_character j r := by
  intro r
  fin_cases r
  · rw [xi_dirichlet_residue_fourier_parseval_exact_sum_modulus,
      xi_dirichlet_residue_fourier_parseval_exact_trace_zero,
      xi_dirichlet_residue_fourier_parseval_exact_trace_one]
    simp [xi_dirichlet_residue_fourier_parseval_exact_character]
    ring
  · rw [xi_dirichlet_residue_fourier_parseval_exact_sum_modulus,
      xi_dirichlet_residue_fourier_parseval_exact_trace_zero,
      xi_dirichlet_residue_fourier_parseval_exact_trace_one]
    simp [xi_dirichlet_residue_fourier_parseval_exact_character]
    ring

private theorem xi_dirichlet_residue_fourier_parseval_exact_parseval
    (counts : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) :
    xi_dirichlet_residue_fourier_parseval_exact_centeredEnergy counts =
      xi_dirichlet_residue_fourier_parseval_exact_nonzeroEnergy counts := by
  let z : ℂ := counts 0 - counts 1
  have h0 :
      xi_dirichlet_residue_fourier_parseval_exact_centered counts 0 = z / 2 := by
    rw [xi_dirichlet_residue_fourier_parseval_exact_centered,
      xi_dirichlet_residue_fourier_parseval_exact_mean,
      xi_dirichlet_residue_fourier_parseval_exact_sum_modulus]
    simp [z]
    ring
  have h1 :
      xi_dirichlet_residue_fourier_parseval_exact_centered counts 1 = -(z / 2) := by
    rw [xi_dirichlet_residue_fourier_parseval_exact_centered,
      xi_dirichlet_residue_fourier_parseval_exact_mean,
      xi_dirichlet_residue_fourier_parseval_exact_sum_modulus]
    simp [z]
    ring
  rw [xi_dirichlet_residue_fourier_parseval_exact_centeredEnergy,
    xi_dirichlet_residue_fourier_parseval_exact_sum_modulus, h0, h1,
    xi_dirichlet_residue_fourier_parseval_exact_nonzeroEnergy,
    xi_dirichlet_residue_fourier_parseval_exact_trace_one, Complex.normSq_neg]
  simpa [z] using (show Complex.normSq z / ((2 : ℝ) * 2) + Complex.normSq z / ((2 : ℝ) * 2) =
    (1 / 2 : ℝ) * Complex.normSq z by ring)

/-- Paper label: `thm:xi-dirichlet-residue-fourier-parseval-exact`. For the concrete modulus-`2`
residue model, the twisted traces are the exact Fourier coefficients, Fourier inversion recovers
the periodic and primitive residue-count functions, and Parseval identifies the centered residue
energy with the unique nonzero Fourier mode. -/
theorem paper_xi_dirichlet_residue_fourier_parseval_exact
    (periodic primitive : xi_dirichlet_residue_fourier_parseval_exact_modulus → ℂ) :
    (∀ r : xi_dirichlet_residue_fourier_parseval_exact_modulus,
      periodic r =
        (1 / (2 : ℂ)) *
          ∑ j, xi_dirichlet_residue_fourier_parseval_exact_trace periodic j *
            xi_dirichlet_residue_fourier_parseval_exact_character j r) ∧
    (∀ r : xi_dirichlet_residue_fourier_parseval_exact_modulus,
      primitive r =
        (1 / (2 : ℂ)) *
          ∑ j, xi_dirichlet_residue_fourier_parseval_exact_trace primitive j *
            xi_dirichlet_residue_fourier_parseval_exact_character j r) ∧
    xi_dirichlet_residue_fourier_parseval_exact_centeredEnergy periodic =
      xi_dirichlet_residue_fourier_parseval_exact_nonzeroEnergy periodic ∧
    xi_dirichlet_residue_fourier_parseval_exact_centeredEnergy primitive =
      xi_dirichlet_residue_fourier_parseval_exact_nonzeroEnergy primitive := by
  refine ⟨xi_dirichlet_residue_fourier_parseval_exact_inversion periodic,
    xi_dirichlet_residue_fourier_parseval_exact_inversion primitive,
    xi_dirichlet_residue_fourier_parseval_exact_parseval periodic,
    xi_dirichlet_residue_fourier_parseval_exact_parseval primitive⟩

end

end Omega.Zeta
