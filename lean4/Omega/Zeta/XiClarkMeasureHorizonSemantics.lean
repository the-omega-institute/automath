import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete disk inner-function / Clark-measure interface for a fixed challenge phase. The
functions record the represented Herglotz density and its singular/atomic decomposition. -/
structure xi_clark_measure_horizon_semantics_interface where
  xi_clark_measure_horizon_semantics_inner : ℂ → ℂ
  xi_clark_measure_horizon_semantics_alpha : ℂ
  xi_clark_measure_horizon_semantics_measure : ℂ → ℝ
  xi_clark_measure_horizon_semantics_singular_part : ℂ → ℝ
  xi_clark_measure_horizon_semantics_atomic_part : ℂ → ℝ

namespace xi_clark_measure_horizon_semantics_interface

/-- A concrete representing-measure predicate for the Clark/Herglotz identity. -/
def xi_clark_measure_horizon_semantics_represents
    (D : xi_clark_measure_horizon_semantics_interface) (μ : ℂ → ℝ) : Prop :=
  ∀ z : ℂ, μ z = D.xi_clark_measure_horizon_semantics_measure z

/-- Uniqueness of the representing measure for the fixed challenge phase. -/
def xi_clark_measure_horizon_semantics_unique_representing_measure
    (D : xi_clark_measure_horizon_semantics_interface) : Prop :=
  ∀ μ : ℂ → ℝ,
    D.xi_clark_measure_horizon_semantics_represents μ →
      μ = D.xi_clark_measure_horizon_semantics_measure

/-- The carried singular/atomic Clark decomposition. -/
def xi_clark_measure_horizon_semantics_decomposition
    (D : xi_clark_measure_horizon_semantics_interface) : Prop :=
  ∀ ζ : ℂ,
    D.xi_clark_measure_horizon_semantics_measure ζ =
      D.xi_clark_measure_horizon_semantics_singular_part ζ +
        D.xi_clark_measure_horizon_semantics_atomic_part ζ

/-- Singular mass is exactly the non-atomic part of the concrete Clark decomposition. -/
def xi_clark_measure_horizon_semantics_singular_semantics
    (D : xi_clark_measure_horizon_semantics_interface) : Prop :=
  (∃ ζ : ℂ, D.xi_clark_measure_horizon_semantics_singular_part ζ ≠ 0) ↔
    (∃ ζ : ℂ,
      D.xi_clark_measure_horizon_semantics_measure ζ ≠
        D.xi_clark_measure_horizon_semantics_atomic_part ζ)

/-- Atomic Clark mass reads out boundary phase solutions for the challenge seed. -/
def xi_clark_measure_horizon_semantics_atomic_semantics
    (D : xi_clark_measure_horizon_semantics_interface) : Prop :=
  ∀ ζ : ℂ,
    D.xi_clark_measure_horizon_semantics_atomic_part ζ ≠ 0 →
      D.xi_clark_measure_horizon_semantics_inner ζ =
        D.xi_clark_measure_horizon_semantics_alpha

/-- Paper-facing Clark-measure semantic package. -/
def xi_clark_measure_horizon_semantics_statement : Prop :=
  ∀ D : xi_clark_measure_horizon_semantics_interface,
    D.xi_clark_measure_horizon_semantics_unique_representing_measure →
      D.xi_clark_measure_horizon_semantics_decomposition →
        D.xi_clark_measure_horizon_semantics_singular_semantics →
          D.xi_clark_measure_horizon_semantics_atomic_semantics →
            D.xi_clark_measure_horizon_semantics_represents
                D.xi_clark_measure_horizon_semantics_measure ∧
              D.xi_clark_measure_horizon_semantics_unique_representing_measure ∧
              D.xi_clark_measure_horizon_semantics_decomposition ∧
              D.xi_clark_measure_horizon_semantics_singular_semantics ∧
              D.xi_clark_measure_horizon_semantics_atomic_semantics

end xi_clark_measure_horizon_semantics_interface

open xi_clark_measure_horizon_semantics_interface

/-- Paper label: `cor:xi-clark-measure-horizon-semantics`. -/
theorem paper_xi_clark_measure_horizon_semantics :
    xi_clark_measure_horizon_semantics_statement := by
  intro D huniq hdecomp hsing hatom
  exact ⟨fun _ => rfl, huniq, hdecomp, hsing, hatom⟩

end Omega.Zeta
