import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Truncated moment profiles of order `n`. -/
abbrev xi_markov_stieltjes_extremal_principle_profile (n : ℕ) :=
  Fin (n + 1) → ℝ

/-- Concrete truncated moment data for the Markov--Stieltjes extremal principle. -/
structure xi_markov_stieltjes_extremal_principle_data where
  xi_markov_stieltjes_extremal_principle_order : ℕ
  xi_markov_stieltjes_extremal_principle_leftEndpoint : ℝ
  xi_markov_stieltjes_extremal_principle_rightEndpoint : ℝ
  xi_markov_stieltjes_extremal_principle_leftProfile :
    xi_markov_stieltjes_extremal_principle_profile
      xi_markov_stieltjes_extremal_principle_order
  xi_markov_stieltjes_extremal_principle_rightProfile :
    xi_markov_stieltjes_extremal_principle_profile
      xi_markov_stieltjes_extremal_principle_order
  xi_markov_stieltjes_extremal_principle_functional :
    xi_markov_stieltjes_extremal_principle_profile
      xi_markov_stieltjes_extremal_principle_order → ℝ
  xi_markov_stieltjes_extremal_principle_leftConvergent : ℝ
  xi_markov_stieltjes_extremal_principle_rightConvergent : ℝ

/-- Endpoint-extreme profiles for the finite truncated moment slice. -/
def xi_markov_stieltjes_extremal_principle_data.endpointExtreme
    (D : xi_markov_stieltjes_extremal_principle_data)
    (μ : xi_markov_stieltjes_extremal_principle_profile
      D.xi_markov_stieltjes_extremal_principle_order) : Prop :=
  D.xi_markov_stieltjes_extremal_principle_functional μ =
      D.xi_markov_stieltjes_extremal_principle_leftEndpoint ∨
    D.xi_markov_stieltjes_extremal_principle_functional μ =
      D.xi_markov_stieltjes_extremal_principle_rightEndpoint

/-- Atomic endpoint witnesses in the finite truncated moment model. -/
def xi_markov_stieltjes_extremal_principle_data.atomicProfile
    (D : xi_markov_stieltjes_extremal_principle_data)
    (μ : xi_markov_stieltjes_extremal_principle_profile
      D.xi_markov_stieltjes_extremal_principle_order) : Prop :=
  μ = D.xi_markov_stieltjes_extremal_principle_leftProfile ∨
    μ = D.xi_markov_stieltjes_extremal_principle_rightProfile

/-- Nevanlinna parameterization of feasible values by the closed endpoint interval. -/
def xi_markov_stieltjes_extremal_principle_data.nevanlinna_parameterization
    (D : xi_markov_stieltjes_extremal_principle_data) : Prop :=
  (∀ t : ℝ,
      t ∈ Set.Icc D.xi_markov_stieltjes_extremal_principle_leftEndpoint
          D.xi_markov_stieltjes_extremal_principle_rightEndpoint ↔
        ∃ μ : xi_markov_stieltjes_extremal_principle_profile
          D.xi_markov_stieltjes_extremal_principle_order,
          D.xi_markov_stieltjes_extremal_principle_functional μ = t) ∧
    D.xi_markov_stieltjes_extremal_principle_functional
        D.xi_markov_stieltjes_extremal_principle_leftProfile =
      D.xi_markov_stieltjes_extremal_principle_leftEndpoint ∧
    D.xi_markov_stieltjes_extremal_principle_functional
        D.xi_markov_stieltjes_extremal_principle_rightProfile =
      D.xi_markov_stieltjes_extremal_principle_rightEndpoint ∧
    D.xi_markov_stieltjes_extremal_principle_leftConvergent =
      D.xi_markov_stieltjes_extremal_principle_leftEndpoint ∧
    D.xi_markov_stieltjes_extremal_principle_rightConvergent =
      D.xi_markov_stieltjes_extremal_principle_rightEndpoint

/-- Endpoint-extreme truncated moment profiles are atomic. -/
def xi_markov_stieltjes_extremal_principle_data.extreme_points_atomic
    (D : xi_markov_stieltjes_extremal_principle_data) : Prop :=
  ∀ μ : xi_markov_stieltjes_extremal_principle_profile
      D.xi_markov_stieltjes_extremal_principle_order,
    D.endpointExtreme μ → D.atomicProfile μ

/-- The feasible values form exactly the Markov--Stieltjes closed interval. -/
def xi_markov_stieltjes_extremal_principle_data.feasible_values_closed_interval
    (D : xi_markov_stieltjes_extremal_principle_data) : Prop :=
  Set.range D.xi_markov_stieltjes_extremal_principle_functional =
    Set.Icc D.xi_markov_stieltjes_extremal_principle_leftEndpoint
      D.xi_markov_stieltjes_extremal_principle_rightEndpoint

/-- The two interval endpoints are the Stieltjes convergents. -/
def xi_markov_stieltjes_extremal_principle_data.endpoints_are_stieltjes_convergents
    (D : xi_markov_stieltjes_extremal_principle_data) : Prop :=
  D.xi_markov_stieltjes_extremal_principle_leftEndpoint =
      D.xi_markov_stieltjes_extremal_principle_leftConvergent ∧
    D.xi_markov_stieltjes_extremal_principle_rightEndpoint =
      D.xi_markov_stieltjes_extremal_principle_rightConvergent

/-- Both Markov--Stieltjes endpoint extrema are atomic profiles. -/
def xi_markov_stieltjes_extremal_principle_data.atomic_extrema
    (D : xi_markov_stieltjes_extremal_principle_data) : Prop :=
  D.atomicProfile D.xi_markov_stieltjes_extremal_principle_leftProfile ∧
    D.atomicProfile D.xi_markov_stieltjes_extremal_principle_rightProfile

/-- Paper label: `prop:xi-markov-stieltjes-extremal-principle`. -/
theorem paper_xi_markov_stieltjes_extremal_principle
    (D : xi_markov_stieltjes_extremal_principle_data)
    (hnev : D.nevanlinna_parameterization)
    (hext : D.extreme_points_atomic) :
    D.feasible_values_closed_interval ∧ D.endpoints_are_stieltjes_convergents ∧
      D.atomic_extrema := by
  rcases hnev with ⟨hRange, hLeft, hRight, hLeftConv, hRightConv⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    constructor
    · intro ht
      exact (hRange t).2 ht
    · intro ht
      exact (hRange t).1 ht
  · exact ⟨hLeftConv.symm, hRightConv.symm⟩
  · exact ⟨hext D.xi_markov_stieltjes_extremal_principle_leftProfile (Or.inl hLeft),
      hext D.xi_markov_stieltjes_extremal_principle_rightProfile (Or.inr hRight)⟩

end

end Omega.Zeta
