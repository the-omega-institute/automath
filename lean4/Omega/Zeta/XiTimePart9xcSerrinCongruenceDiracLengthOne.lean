import Omega.Zeta.XiTimePart9xcSerrinLdpVacuum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

def xi_time_part9xc_serrin_congruence_dirac_length_one_birkhoff_sum (e₀ n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun _ => e₀

def xi_time_part9xc_serrin_congruence_dirac_length_one_dirac_distribution (e₀ n m : ℕ) :
    ZMod m → ℕ :=
  fun r => if r = ((n * e₀ : ℕ) : ZMod m) then 1 else 0

def xi_time_part9xc_serrin_congruence_dirac_length_one_periodic_weight (e₀ n : ℕ) (u : ℂ) : ℂ :=
  u ^ (n * e₀)

def xi_time_part9xc_serrin_congruence_dirac_length_one_primitive_weight (e₀ : ℕ) (u : ℂ) :
    ℕ → ℂ
  | 0 => 0
  | 1 => u ^ e₀
  | _ + 2 => 0

def xi_time_part9xc_serrin_congruence_dirac_length_one_birkhoff_sum_closed_form (e₀ n : ℕ) :
    Prop :=
  xi_time_part9xc_serrin_congruence_dirac_length_one_birkhoff_sum e₀ n = n * e₀

def xi_time_part9xc_serrin_congruence_dirac_length_one_mod_distribution_dirac
    (e₀ n m : ℕ) : Prop :=
  xi_time_part9xc_serrin_congruence_dirac_length_one_dirac_distribution e₀ n m
      (((n * e₀ : ℕ) : ZMod m)) = 1 ∧
    ∀ r : ZMod m, r ≠ ((n * e₀ : ℕ) : ZMod m) →
      xi_time_part9xc_serrin_congruence_dirac_length_one_dirac_distribution e₀ n m r = 0

def xi_time_part9xc_serrin_congruence_dirac_length_one_primitive_length_one
    (e₀ n : ℕ) (u : ℂ) : Prop :=
  xi_time_part9xc_serrin_congruence_dirac_length_one_periodic_weight e₀ n u = u ^ (n * e₀) ∧
    xi_time_part9xc_serrin_congruence_dirac_length_one_primitive_weight e₀ u 1 = u ^ e₀ ∧
    ∀ k, xi_time_part9xc_serrin_congruence_dirac_length_one_primitive_weight e₀ u (k + 2) = 0

/-- `thm:xi-time-part9xc-serrin-congruence-dirac-length-one` -/
theorem paper_xi_time_part9xc_serrin_congruence_dirac_length_one (e₀ n m : ℕ) (u : ℂ) :
    xi_time_part9xc_serrin_congruence_dirac_length_one_birkhoff_sum_closed_form e₀ n ∧
      xi_time_part9xc_serrin_congruence_dirac_length_one_mod_distribution_dirac e₀ n m ∧
      xi_time_part9xc_serrin_congruence_dirac_length_one_primitive_length_one e₀ n u := by
  constructor
  · simp [xi_time_part9xc_serrin_congruence_dirac_length_one_birkhoff_sum_closed_form,
      xi_time_part9xc_serrin_congruence_dirac_length_one_birkhoff_sum, Nat.mul_comm]
  · constructor
    · constructor
      · simp [xi_time_part9xc_serrin_congruence_dirac_length_one_dirac_distribution]
      · intro r hr
        simp only [xi_time_part9xc_serrin_congruence_dirac_length_one_dirac_distribution]
        split_ifs with h
        · exact False.elim (hr h)
        · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · intro k
          rfl

end Omega.Zeta
