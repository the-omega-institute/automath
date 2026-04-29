import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart28CEndpointFluxExponentialCylinderContinuity

namespace Omega.Zeta

/-- Concrete stabilized finite-prefix data for the endpoint-flux Cauchy modulus.  The finite
coefficient table stabilizes coordinatewise after `threshold n`; the endpoint flux at scale `N`
is exponentially close to its limiting endpoint value once all coordinates up to `N` have
stabilized. -/
structure xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data where
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_prefixCoeff : ℕ → ℕ → ℂ
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_limitCoeff : ℕ → ℂ
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold : ℕ → ℕ
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_flux : ℕ → ℕ → ℝ
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_limitFlux : ℕ → ℝ
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_C : ℝ
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_q : ℝ
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_coeffStabilizes :
    ∀ n L,
      xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold n ≤ L →
        xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_prefixCoeff L n =
          xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_limitCoeff n
  xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_fluxEstimate :
    ∀ N L,
      (∀ n, n ≤ N →
        xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold n ≤ L) →
        |xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_flux L N -
          xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_limitFlux N| ≤
          xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_C *
            xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_q ^ N

namespace xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data

/-- The finite maximum of coordinate stabilization thresholds through coordinate `N`. -/
def xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_Lstar
    (D : xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data) : ℕ → ℕ
  | 0 => D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold 0
  | N + 1 =>
      max (xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_Lstar D N)
        (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold (N + 1))

lemma xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold_le_Lstar
    (D : xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data) :
    ∀ {n N : ℕ}, n ≤ N →
      D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold n ≤
        xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_Lstar D N := by
  intro n N hn
  induction N with
  | zero =>
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst hn0
      rfl
  | succ N ih =>
      by_cases hlast : n = N + 1
      · subst hlast
        exact le_max_right _ _
      · have hnN : n ≤ N := by omega
        exact le_trans (ih hnN) (le_max_left _ _)

/-- All coefficients in the prefix through `N` have stabilized by `L_*(N)`. -/
def eventualPrefixStabilizes
    (D : xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data) : Prop :=
  ∀ N n L,
    n ≤ N →
      xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_Lstar D N ≤ L →
        D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_prefixCoeff L n =
          D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_limitCoeff n

/-- The finite-CMV endpoint-flux estimate transfers to the limiting object after `L_*(N)`. -/
def exponentialLimitBound
    (D : xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data) : Prop :=
  ∀ N L,
    xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_Lstar D N ≤ L →
      |D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_flux L N -
        D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_limitFlux N| ≤
        D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_C *
          D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_q ^ N

/-- The stabilized endpoint fluxes are Cauchy with the explicit exponential modulus. -/
def cauchyModulus
    (D : xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data) : Prop :=
  ∀ N L₁ L₂,
    xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_Lstar D N ≤ L₁ →
      xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_Lstar D N ≤ L₂ →
        |D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_flux L₁ N -
          D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_flux L₂ N| ≤
          2 * D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_C *
            D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_q ^ N

end xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data

/-- Paper label: `cor:xi-time-part28c-stabilized-endpoint-flux-cauchy-modulus`. -/
theorem paper_xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus
    (D : xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_data) :
    D.eventualPrefixStabilizes ∧ D.exponentialLimitBound ∧ D.cauchyModulus := by
  refine ⟨?_, ?_, ?_⟩
  · intro N n L hn hL
    exact D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_coeffStabilizes n L
      (le_trans
        (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold_le_Lstar hn)
        hL)
  · intro N L hL
    exact D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_fluxEstimate N L
      (fun n hn =>
        le_trans
          (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold_le_Lstar hn)
          hL)
  · intro N L₁ L₂ hL₁ hL₂
    exact paper_xi_time_part28c_endpoint_flux_exponential_cylinder_continuity N
      (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_flux L₁ N)
      (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_flux L₂ N)
      (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_limitFlux N)
      D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_C
      D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_q
      (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_fluxEstimate N L₁
        (fun n hn =>
          le_trans
            (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold_le_Lstar hn)
            hL₁))
      (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_fluxEstimate N L₂
        (fun n hn =>
          le_trans
            (D.xi_time_part28c_stabilized_endpoint_flux_cauchy_modulus_threshold_le_Lstar hn)
            hL₂))

end Omega.Zeta
