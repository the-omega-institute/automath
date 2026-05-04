import Mathlib.Data.Nat.Basic

namespace Omega.Zeta

/-- Product of a finite list of natural numbers, kept local to this paper label. -/
def xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct : List ℕ → ℕ
  | [] => 1
  | n :: ns => n * xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct ns

/-- The local list product is multiplicative under append. -/
lemma xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct_append
    (left right : List ℕ) :
    xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct (left ++ right) =
      xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct left *
        xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct right := by
  induction left with
  | nil =>
      simp [xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct]
  | cons head tail ih =>
      simp [xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct, ih,
        Nat.mul_assoc]

/-- Prime-power Smith-kernel count for a finite list of Smith exponents. -/
def xi_kernel_dirichlet_zeta_finite_euler_correction_primePowerKernel
    (p : ℕ) (exponents : List ℕ) (k : ℕ) : ℕ :=
  xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct
    (exponents.map fun e => p ^ min k e)

/-- Finite Euler correction obtained by summing the prime-power kernel counts up to `height`. -/
def xi_kernel_dirichlet_zeta_finite_euler_correction_finiteEulerCorrection
    (p : ℕ) (exponents : List ℕ) (height : ℕ) : ℕ :=
  ((List.range (height + 1)).map fun k =>
    xi_kernel_dirichlet_zeta_finite_euler_correction_primePowerKernel p exponents k).sum

/-- The finite-support correction is trivial away from the recorded bad-prime list. -/
def xi_kernel_dirichlet_zeta_finite_euler_correction_badPrimeCorrection
    (badPrimes : List ℕ) (p : ℕ) : ℕ :=
  if p ∈ badPrimes then badPrimes.length + 1 else 1

/-- Concrete statement for the finite Euler correction theorem. -/
def xi_kernel_dirichlet_zeta_finite_euler_correction_statement : Prop :=
  (∀ (p : ℕ) (left right : List ℕ) (k : ℕ),
      xi_kernel_dirichlet_zeta_finite_euler_correction_primePowerKernel
          p (left ++ right) k =
        xi_kernel_dirichlet_zeta_finite_euler_correction_primePowerKernel p left k *
          xi_kernel_dirichlet_zeta_finite_euler_correction_primePowerKernel p right k) ∧
    (∀ (p : ℕ) (exponents : List ℕ) (height : ℕ),
      xi_kernel_dirichlet_zeta_finite_euler_correction_finiteEulerCorrection
          p exponents height =
        ((List.range (height + 1)).map fun k =>
          xi_kernel_dirichlet_zeta_finite_euler_correction_primePowerKernel p exponents k).sum) ∧
      ∀ (badPrimes : List ℕ) (p : ℕ),
        p ∉ badPrimes →
          xi_kernel_dirichlet_zeta_finite_euler_correction_badPrimeCorrection badPrimes p = 1

/-- Paper label: `thm:xi-kernel-dirichlet-zeta-finite-euler-correction`. -/
theorem paper_xi_kernel_dirichlet_zeta_finite_euler_correction :
    xi_kernel_dirichlet_zeta_finite_euler_correction_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro p left right k
    simp [xi_kernel_dirichlet_zeta_finite_euler_correction_primePowerKernel,
      List.map_append, xi_kernel_dirichlet_zeta_finite_euler_correction_natListProduct_append]
  · intro p exponents height
    rfl
  · intro badPrimes p hp
    simp [xi_kernel_dirichlet_zeta_finite_euler_correction_badPrimeCorrection, hp]

end Omega.Zeta
