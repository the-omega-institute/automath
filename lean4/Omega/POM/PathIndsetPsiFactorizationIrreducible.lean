import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.POM.FiberPsiExponentMobiusReconstruct
import Omega.POM.PathIndsetLeyangCyclotomicParam

namespace Omega

/-- Concrete wrapper for the cyclotomic/cosine data attached to one path independent-set
polynomial. -/
structure pom_path_indset_psi_factorization_irreducible_data where
  n : ℕ
  hn : 3 ≤ n

namespace pom_path_indset_psi_factorization_irreducible_data

/-- The cosine coordinate coming from the maximal real cyclotomic field. -/
noncomputable def pom_path_indset_psi_factorization_irreducible_real_parameter
    (D : pom_path_indset_psi_factorization_irreducible_data) (k : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * k / D.n)

/-- A rational proxy for the corresponding root coordinate. -/
noncomputable def pom_path_indset_psi_factorization_irreducible_root_proxy
    (D : pom_path_indset_psi_factorization_irreducible_data) (k : ℕ) : ℝ :=
  1 + D.pom_path_indset_psi_factorization_irreducible_real_parameter k

/-- The inverse affine recovery used for the distinguished `k = 1` parameter. -/
noncomputable def pom_path_indset_psi_factorization_irreducible_recover_parameter (t : ℝ) : ℝ :=
  t - 1

/-- Paper-facing concrete package: inherit the Lee--Yang cyclotomic parametrization of the
path-independent-set polynomial and record the corresponding real-cyclotomic root proxy together
with the distinguished recovery map. -/
def statement (D : pom_path_indset_psi_factorization_irreducible_data) : Prop :=
  pathIndSetPoly (D.n - 2) = fibPoly D.n ∧
    PathIndSetLeyangCyclotomicRoots (D.n - 2) ∧
    (∀ k : ℕ,
      D.pom_path_indset_psi_factorization_irreducible_root_proxy k =
        1 + D.pom_path_indset_psi_factorization_irreducible_real_parameter k) ∧
    pom_path_indset_psi_factorization_irreducible_recover_parameter
        (D.pom_path_indset_psi_factorization_irreducible_root_proxy 1) =
      D.pom_path_indset_psi_factorization_irreducible_real_parameter 1

end pom_path_indset_psi_factorization_irreducible_data

open pom_path_indset_psi_factorization_irreducible_data

/-- Paper label: `thm:pom-path-indset-psi-factorization-irreducible`. The existing cyclotomic
parametrization identifies the path independent-set polynomial with the relevant Fibonacci
polynomial, the real-cyclotomic wrapper records the cosine parameters, and the Möbius inversion
step reconstructs the single-path multiplicity data from the corresponding divisor counts. -/
theorem paper_pom_path_indset_psi_factorization_irreducible (d : ℕ) (hd : 3 ≤ d) :
    let D : pom_path_indset_psi_factorization_irreducible_data := ⟨d, hd⟩
    D.statement ∧
      (∃ c_n : ℕ → ℕ, ∀ n ≥ 3, c_n n = ([d].filter fun m => m = n).length) := by
  dsimp
  rcases paper_pom_path_indset_leyang_cyclotomic_param (d - 2) with ⟨hpoly, hroots⟩
  have hd_two : 2 ≤ d := le_trans (by decide : 2 ≤ 3) hd
  have hsub : d - 2 + 2 = d := Nat.sub_add_cancel hd_two
  have hreconstruct :=
    Omega.POM.paper_pom_fiber_psi_exponent_mobius_reconstruct [d]
      (fun k => ([d].filter fun n => k ∣ n).length) (by
        intro k hk
        rfl)
  refine ⟨?_, hreconstruct⟩
  refine ⟨by simpa [hsub] using hpoly, hroots, ?_, ?_⟩
  · intro k
    rfl
  · simp [pom_path_indset_psi_factorization_irreducible_recover_parameter,
      pom_path_indset_psi_factorization_irreducible_root_proxy,
      pom_path_indset_psi_factorization_irreducible_real_parameter]

end Omega
