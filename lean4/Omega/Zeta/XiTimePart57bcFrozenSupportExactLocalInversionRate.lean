import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.BinfoldExactInversionUpperEndpointFreezingSlope

open Filter

namespace Omega.Zeta

/-- Concrete frozen-support input: the maximal fiber family is the geometric law `M_m = b^m`. -/
structure xi_time_part57bc_frozen_support_exact_local_inversion_rate_data where
  xi_time_part57bc_frozen_support_exact_local_inversion_rate_base : ℕ
  xi_time_part57bc_frozen_support_exact_local_inversion_rate_base_ge_one :
    1 ≤ xi_time_part57bc_frozen_support_exact_local_inversion_rate_base

/-- The maximal frozen-support fiber size `M_m`. -/
def xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) (m : ℕ) : ℕ :=
  D.xi_time_part57bc_frozen_support_exact_local_inversion_rate_base ^ m

/-- The exact local side-information budget used on the maximal frozen-support fiber. -/
noncomputable def xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) (m : ℕ) : ℕ :=
  Omega.Conclusion.binfoldUpperEndpointBudget
    D.xi_time_part57bc_frozen_support_exact_local_inversion_rate_base m

/-- Exact local inversion at budget `B` is an injective binary encoding of the maximal fiber into
`2^B` labels. -/
def xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) (m B : ℕ) : Prop :=
  Nonempty
    (Fin (xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber D m) ↪
      Fin (2 ^ B))

/-- The max-fiber exponent `α_* = log b` in the geometric model `M_m = b^m`. -/
noncomputable def xi_time_part57bc_frozen_support_exact_local_inversion_rate_alpha_star
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) : ℝ :=
  Real.log (D.xi_time_part57bc_frozen_support_exact_local_inversion_rate_base : ℝ)

private lemma xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget_eq_clog
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) (m : ℕ) :
    xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m =
      Nat.clog 2 (xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber D m) := by
  unfold xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget
  unfold xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber
  rw [Omega.Conclusion.binfoldUpperEndpointBudget_formula]
  simpa using
    (Real.natCeil_logb_natCast 2
      (D.xi_time_part57bc_frozen_support_exact_local_inversion_rate_base ^ m))

private lemma xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits_bit_budget
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) (m : ℕ) :
    xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits D m
      (xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m) := by
  rw [xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget_eq_clog]
  unfold xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits
  have hpow :
      xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber D m ≤
        2 ^ Nat.clog 2 (xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber D m) :=
    Nat.le_pow_clog (by norm_num) _
  exact ⟨Fin.castLEEmb hpow⟩

private lemma xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget_minimal
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) (m B : ℕ)
    (hB : xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits D m B) :
    xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m ≤ B := by
  rw [xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget_eq_clog]
  have hcard :
      xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber D m ≤ 2 ^ B := by
    rcases hB with ⟨e⟩
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  exact Nat.clog_le_of_le_pow hcard

private lemma xi_time_part57bc_frozen_support_exact_local_inversion_rate_limit
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) :
    Tendsto
      (fun m : ℕ =>
        (xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m : ℝ) / m)
      atTop
      (nhds
        (xi_time_part57bc_frozen_support_exact_local_inversion_rate_alpha_star D / Real.log 2)) := by
  have hlimit :=
    Omega.Conclusion.binfoldUpperEndpointBudget_limit
      D.xi_time_part57bc_frozen_support_exact_local_inversion_rate_base
      D.xi_time_part57bc_frozen_support_exact_local_inversion_rate_base_ge_one
  simpa [Omega.Conclusion.binfoldFreezingSlope,
    xi_time_part57bc_frozen_support_exact_local_inversion_rate_alpha_star, Real.log_div_log] using
    hlimit

/-- Frozen-support exact local inversion budget = `⌈log₂ M_m⌉`, together with the corresponding
asymptotic bitrate. -/
def xi_time_part57bc_frozen_support_exact_local_inversion_rate_statement
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) : Prop :=
  (∀ m : ℕ,
    xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits D m
      (xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m)) ∧
    (∀ m B : ℕ,
      xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits D m B →
        xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m ≤ B) ∧
    (∀ m : ℕ,
      xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m =
        Nat.ceil
          (Real.log
            (xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber D m : ℝ) /
            Real.log 2)) ∧
    Tendsto
      (fun m : ℕ =>
        (xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget D m : ℝ) / m)
      atTop
      (nhds
        (xi_time_part57bc_frozen_support_exact_local_inversion_rate_alpha_star D / Real.log 2))

/-- Paper label: `thm:xi-time-part57bc-frozen-support-exact-local-inversion-rate`. Counting gives
the lower bound `2^B ≥ M_m`, the canonical embedding `Fin M_m ↪ Fin (2^B)` at
`B = ⌈log₂ M_m⌉` gives attainability, and the geometric max-fiber law turns the normalized budget
into the exact rate `α_* / log 2`. -/
theorem paper_xi_time_part57bc_frozen_support_exact_local_inversion_rate
    (D : xi_time_part57bc_frozen_support_exact_local_inversion_rate_data) :
    xi_time_part57bc_frozen_support_exact_local_inversion_rate_statement D := by
  refine ⟨?_, ?_, ?_, xi_time_part57bc_frozen_support_exact_local_inversion_rate_limit D⟩
  · intro m
    exact xi_time_part57bc_frozen_support_exact_local_inversion_rate_admits_bit_budget D m
  · intro m B hB
    exact xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget_minimal D m B hB
  · intro m
    rw [xi_time_part57bc_frozen_support_exact_local_inversion_rate_bit_budget_eq_clog]
    simpa [Real.log_div_log] using
      (Real.natCeil_logb_natCast 2
        (xi_time_part57bc_frozen_support_exact_local_inversion_rate_max_fiber D m)).symm

end Omega.Zeta
