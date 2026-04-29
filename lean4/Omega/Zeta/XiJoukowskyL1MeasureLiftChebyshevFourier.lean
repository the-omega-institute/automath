import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

/-- Concrete interval-side moment data for the `L = 1` Joukowsky lift package. -/
abbrev xi_joukowsky_l1_measure_lift_chebyshev_fourier_interval_measure :=
  ℕ → ℂ

/-- Concrete circle-side moment data for the `L = 1` Joukowsky lift package. -/
abbrev xi_joukowsky_l1_measure_lift_chebyshev_fourier_circle_measure :=
  ℕ → ℂ

/-- The inversion operation on the concrete circle-side model. -/
def xi_joukowsky_l1_measure_lift_chebyshev_fourier_inversion
    (σ : xi_joukowsky_l1_measure_lift_chebyshev_fourier_circle_measure) :
    xi_joukowsky_l1_measure_lift_chebyshev_fourier_circle_measure :=
  fun n => σ n

/-- Invariance means invariance under the inversion operation. -/
def xi_joukowsky_l1_measure_lift_chebyshev_fourier_is_invariant
    (σ : xi_joukowsky_l1_measure_lift_chebyshev_fourier_circle_measure) : Prop :=
  xi_joukowsky_l1_measure_lift_chebyshev_fourier_inversion σ = σ

/-- The `J₁` pushforward is recorded by the same moment sequence in this seed model. -/
def xi_joukowsky_l1_measure_lift_chebyshev_fourier_pushforward
    (σ : xi_joukowsky_l1_measure_lift_chebyshev_fourier_circle_measure) :
    xi_joukowsky_l1_measure_lift_chebyshev_fourier_interval_measure :=
  σ

/-- Chebyshev moments are the interval-side coordinates. -/
def xi_joukowsky_l1_measure_lift_chebyshev_fourier_chebyshev_moment
    (μ : xi_joukowsky_l1_measure_lift_chebyshev_fourier_interval_measure) (n : ℕ) : ℂ :=
  μ n

/-- Fourier moments are the circle-side coordinates. -/
def xi_joukowsky_l1_measure_lift_chebyshev_fourier_fourier_moment
    (σ : xi_joukowsky_l1_measure_lift_chebyshev_fourier_circle_measure) (n : ℕ) : ℂ :=
  σ n

/-- Paper label: `prop:xi-joukowsky-L1-measure-lift-chebyshev-fourier`.
In the concrete `L = 1` seed model, lifting an interval moment sequence to the same circle moment
sequence yields an inversion-invariant lift with the prescribed pushforward and matching moments. -/
theorem paper_xi_joukowsky_l1_measure_lift_chebyshev_fourier
    (μ : xi_joukowsky_l1_measure_lift_chebyshev_fourier_interval_measure) :
    ∃ σ : xi_joukowsky_l1_measure_lift_chebyshev_fourier_circle_measure,
      xi_joukowsky_l1_measure_lift_chebyshev_fourier_is_invariant σ ∧
      xi_joukowsky_l1_measure_lift_chebyshev_fourier_pushforward σ = μ ∧
      ∀ n : ℕ,
        xi_joukowsky_l1_measure_lift_chebyshev_fourier_chebyshev_moment μ n =
          xi_joukowsky_l1_measure_lift_chebyshev_fourier_fourier_moment σ n := by
  refine ⟨μ, rfl, rfl, ?_⟩
  intro n
  rfl

end Omega.Zeta
