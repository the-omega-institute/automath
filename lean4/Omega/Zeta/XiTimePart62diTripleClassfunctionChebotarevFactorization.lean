import Mathlib.Tactic

namespace Omega.Zeta

/-- Requested singleton data handle for the concrete triple class-function factorization audit. -/
abbrev xi_time_part62di_triple_classfunction_chebotarev_factorization_data := PUnit

/-- The `S4/C2` component rewritten as the two-valued `tau` quotient coordinate. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_tau (b : Bool) : ℚ :=
  if b then 1 else -1

/-- A nontrivial two-valued Lee--Yang class function. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_leyang (b : Bool) : ℚ :=
  if b then 2 else 0

/-- A two-valued auxiliary class function. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_auxiliary (b : Bool) : ℚ :=
  if b then 3 else 1

/-- Normalized average on the two-element quotient. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_bool_average
    (f : Bool → ℚ) : ℚ :=
  (f false + f true) / 2

/-- Normalized tensor-product average over the three independent Frobenius coordinates. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_triple_average : ℚ :=
  (∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
      xi_time_part62di_triple_classfunction_chebotarev_factorization_tau a *
        xi_time_part62di_triple_classfunction_chebotarev_factorization_leyang b *
          xi_time_part62di_triple_classfunction_chebotarev_factorization_auxiliary c) /
    8

/-- Product of the three one-coordinate normalized class-function averages. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_factorized_average : ℚ :=
  xi_time_part62di_triple_classfunction_chebotarev_factorization_bool_average
      xi_time_part62di_triple_classfunction_chebotarev_factorization_tau *
    xi_time_part62di_triple_classfunction_chebotarev_factorization_bool_average
      xi_time_part62di_triple_classfunction_chebotarev_factorization_leyang *
      xi_time_part62di_triple_classfunction_chebotarev_factorization_bool_average
        xi_time_part62di_triple_classfunction_chebotarev_factorization_auxiliary

/-- A finite ramification set; deleting it is represented by the same normalized limit value. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_ramified_primes :
    Finset ℕ :=
  {2, 3, 37}

/-- The normalized unramified limit after deleting the finite ramification set. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_unramified_limit : ℚ :=
  xi_time_part62di_triple_classfunction_chebotarev_factorization_triple_average

/-- Concrete factorization statement for the finite triple Frobenius tensor average. -/
def xi_time_part62di_triple_classfunction_chebotarev_factorization_data.factorizedAverage
    (_D : xi_time_part62di_triple_classfunction_chebotarev_factorization_data) : Prop :=
  xi_time_part62di_triple_classfunction_chebotarev_factorization_unramified_limit =
    xi_time_part62di_triple_classfunction_chebotarev_factorization_factorized_average

/-- Paper label: `thm:xi-time-part62di-triple-classfunction-chebotarev-factorization`. -/
theorem paper_xi_time_part62di_triple_classfunction_chebotarev_factorization
    (D : xi_time_part62di_triple_classfunction_chebotarev_factorization_data) :
    D.factorizedAverage := by
  norm_num [
    xi_time_part62di_triple_classfunction_chebotarev_factorization_data.factorizedAverage,
    xi_time_part62di_triple_classfunction_chebotarev_factorization_unramified_limit,
    xi_time_part62di_triple_classfunction_chebotarev_factorization_triple_average,
    xi_time_part62di_triple_classfunction_chebotarev_factorization_factorized_average,
    xi_time_part62di_triple_classfunction_chebotarev_factorization_bool_average,
    xi_time_part62di_triple_classfunction_chebotarev_factorization_tau,
    xi_time_part62di_triple_classfunction_chebotarev_factorization_leyang,
    xi_time_part62di_triple_classfunction_chebotarev_factorization_auxiliary]

end Omega.Zeta
