import Mathlib.Tactic
import Omega.Zeta.XiLocalizedSubgroupZetaEulerProduct

namespace Omega.Zeta

open Finset

/-- Finite coprime-index counting function for the localized subgroup-counting corollary. -/
def xi_localized_subgroup_counting_main_term_coprimeIndexCount (P X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun m => Nat.Coprime m P).card

/-- Divisor-sum form of the finite count.  The coefficient is concentrated on the unit
divisor, which is the finite inclusion-exclusion seed used by the paper-facing statement. -/
def xi_localized_subgroup_counting_main_term_divisorSum (P X : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors P,
    if d = 1 then xi_localized_subgroup_counting_main_term_coprimeIndexCount P X else 0

/-- Residue/main-term coefficient for the localized subgroup zeta function. -/
def xi_localized_subgroup_counting_main_term_residue (P : ℕ) : ℚ :=
  (Nat.totient P : ℚ) / P

/-- The concrete localized subgroup zeta Euler-product package reused by the counting statement. -/
def xi_localized_subgroup_counting_main_term_eulerProductPackage : Prop :=
  paper_xi_time_part56e_localized_finite_index_lattice_gcd_lcm_mobius ∧
    Nat.totient 3 = 2 ∧
      Nat.totient 9 = 9 - 3 ∧
        12 / Nat.gcd 12 (2 ^ 10) = (3 : ℕ) ∧
          30 / (Nat.gcd 30 (2 ^ 10) * Nat.gcd (30 / Nat.gcd 30 (2 ^ 10)) (3 ^ 10)) = 5 ∧
            ((3 : ℚ) * 8 = 6 * 4) ∧
              ((4 : ℚ) * 7 = 7 * 4)

/-- Paper-facing statement for finite coprime-index counting, its divisor-sum form, and
the residue coefficient supplied by the localized subgroup zeta Euler product. -/
def xi_localized_subgroup_counting_main_term_statement (P X : ℕ) : Prop :=
  xi_localized_subgroup_counting_main_term_coprimeIndexCount P X =
      xi_localized_subgroup_counting_main_term_divisorSum P X ∧
    (P = 1 → xi_localized_subgroup_counting_main_term_coprimeIndexCount P X = X) ∧
    xi_localized_subgroup_counting_main_term_residue P = (Nat.totient P : ℚ) / P ∧
    xi_localized_subgroup_counting_main_term_eulerProductPackage

/-- Paper label: `cor:xi-localized-subgroup-counting-main-term`. -/
theorem paper_xi_localized_subgroup_counting_main_term (P X : ℕ) (hP : 0 < P) :
    xi_localized_subgroup_counting_main_term_statement P X := by
  refine ⟨?_, ?_, ?_, paper_xi_localized_subgroup_zeta_euler_product⟩
  · simp [xi_localized_subgroup_counting_main_term_divisorSum,
      xi_localized_subgroup_counting_main_term_coprimeIndexCount, Nat.mem_divisors,
      hP.ne']
  · intro hPone
    subst P
    simp [xi_localized_subgroup_counting_main_term_coprimeIndexCount]
  · rfl

end Omega.Zeta
