import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Finite pole ledger for the radial Carathéodory wall-crossing count. -/
structure xi_carath_radial_wallcrossing_data where
  poles : Finset ℕ
  radius : ℕ → ℝ
  multiplicity : ℕ → ℕ
  ambientRadius : ℝ
  radius_positive : ∀ p ∈ poles, 0 < radius p
  radius_lt_ambient : ∀ p ∈ poles, radius p < ambientRadius

/-- Radial index: total pole multiplicity strictly inside radius `r`. -/
def xi_carath_radial_wallcrossing_radialIndex
    (D : xi_carath_radial_wallcrossing_data) (r : ℝ) : ℕ :=
  (D.poles.filter (fun p => D.radius p < r)).sum D.multiplicity

/-- Multiplicity carried by the half-open annulus `[r,s)`. -/
def xi_carath_radial_wallcrossing_shellMultiplicity
    (D : xi_carath_radial_wallcrossing_data) (r s : ℝ) : ℕ :=
  (D.poles.filter (fun p => r ≤ D.radius p ∧ D.radius p < s)).sum D.multiplicity

/-- Multiplicity of poles exactly on a radial wall. -/
def xi_carath_radial_wallcrossing_wallMultiplicity
    (D : xi_carath_radial_wallcrossing_data) (ρ : ℝ) : ℕ :=
  (D.poles.filter (fun p => D.radius p = ρ)).sum D.multiplicity

lemma xi_carath_radial_wallcrossing_filter_split
    (D : xi_carath_radial_wallcrossing_data) {r s : ℝ} (hrs : r ≤ s) :
    D.poles.filter (fun p => D.radius p < s) =
      D.poles.filter (fun p => D.radius p < r) ∪
        D.poles.filter (fun p => r ≤ D.radius p ∧ D.radius p < s) := by
  classical
  ext p
  by_cases hp : p ∈ D.poles
  · by_cases hpr : D.radius p < r
    · simp [hp, hpr, lt_of_lt_of_le hpr hrs]
    · have hr_le : r ≤ D.radius p := le_of_not_gt hpr
      by_cases hps : D.radius p < s
      · simp [hp, hpr, hps, hr_le]
      · simp [hp, hpr, hps]
  · simp [hp]

lemma xi_carath_radial_wallcrossing_filter_disjoint
    (D : xi_carath_radial_wallcrossing_data) (r s : ℝ) :
    Disjoint (D.poles.filter fun p => D.radius p < r)
      (D.poles.filter fun p => r ≤ D.radius p ∧ D.radius p < s) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpLeft hpRight
  have hlt : D.radius p < r := (Finset.mem_filter.mp hpLeft).2
  have hle : r ≤ D.radius p := (Finset.mem_filter.mp hpRight).2.1
  exact (not_lt_of_ge hle) hlt

lemma xi_carath_radial_wallcrossing_index_split
    (D : xi_carath_radial_wallcrossing_data) {r s : ℝ} (hrs : r ≤ s) :
    xi_carath_radial_wallcrossing_radialIndex D s =
      xi_carath_radial_wallcrossing_radialIndex D r +
        xi_carath_radial_wallcrossing_shellMultiplicity D r s := by
  classical
  rw [xi_carath_radial_wallcrossing_radialIndex,
    xi_carath_radial_wallcrossing_radialIndex,
    xi_carath_radial_wallcrossing_shellMultiplicity,
    xi_carath_radial_wallcrossing_filter_split D hrs,
    Finset.sum_union (xi_carath_radial_wallcrossing_filter_disjoint D r s)]

lemma xi_carath_radial_wallcrossing_monotone
    (D : xi_carath_radial_wallcrossing_data) {r s : ℝ} (hrs : r ≤ s) :
    xi_carath_radial_wallcrossing_radialIndex D r ≤
      xi_carath_radial_wallcrossing_radialIndex D s := by
  rw [xi_carath_radial_wallcrossing_index_split D hrs]
  exact Nat.le_add_right _ _

lemma xi_carath_radial_wallcrossing_shell_eq_wall
    (D : xi_carath_radial_wallcrossing_data) (ρ ε : ℝ) (hε : 0 < ε)
    (hgap :
      ∀ p ∈ D.poles, D.radius p ≠ ρ → ¬ (ρ < D.radius p ∧ D.radius p < ρ + ε)) :
    xi_carath_radial_wallcrossing_shellMultiplicity D ρ (ρ + ε) =
      xi_carath_radial_wallcrossing_wallMultiplicity D ρ := by
  classical
  unfold xi_carath_radial_wallcrossing_shellMultiplicity
    xi_carath_radial_wallcrossing_wallMultiplicity
  apply Finset.sum_congr
  · ext p
    by_cases hp : p ∈ D.poles
    · by_cases hρ : D.radius p = ρ
      · simp [hp, hρ, hε]
      · have hnot : ¬ (ρ < D.radius p ∧ D.radius p < ρ + ε) := hgap p hp hρ
        by_cases hle : ρ ≤ D.radius p
        · have hnot_lt : ¬ D.radius p < ρ + ε := by
            intro hlt
            exact hnot ⟨lt_of_le_of_ne hle (Ne.symm hρ), hlt⟩
          simp [hp, hρ, hle, hnot_lt]
        · have hnot_le : ¬ ρ ≤ D.radius p := hle
          simp [hp, hρ, hnot_le]
    · simp [hp]
  · intro p _
    rfl

/-- Paper-facing statement: finite pole ledgers give monotonic radial indices, exact annulus
splitting, and wall jumps equal to the multiplicity on the crossed radius. -/
def xi_carath_radial_wallcrossing_statement
    (D : xi_carath_radial_wallcrossing_data) : Prop :=
  (∀ r s : ℝ, r ≤ s →
      xi_carath_radial_wallcrossing_radialIndex D r ≤
        xi_carath_radial_wallcrossing_radialIndex D s) ∧
    (∀ r s : ℝ, r ≤ s →
      xi_carath_radial_wallcrossing_radialIndex D s =
        xi_carath_radial_wallcrossing_radialIndex D r +
          xi_carath_radial_wallcrossing_shellMultiplicity D r s) ∧
      ∀ ρ ε : ℝ, 0 < ε →
        (∀ p ∈ D.poles, D.radius p ≠ ρ →
          ¬ (ρ < D.radius p ∧ D.radius p < ρ + ε)) →
          xi_carath_radial_wallcrossing_radialIndex D (ρ + ε) =
            xi_carath_radial_wallcrossing_radialIndex D ρ +
              xi_carath_radial_wallcrossing_wallMultiplicity D ρ

/-- Paper label: `thm:xi-carath-radial-wallcrossing`. A finite pole ledger makes the radial
Carathéodory index a monotone step function, with jumps computed by the pole multiplicities on
the crossed wall. -/
theorem paper_xi_carath_radial_wallcrossing (D : xi_carath_radial_wallcrossing_data) :
    xi_carath_radial_wallcrossing_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro r s hrs
    exact xi_carath_radial_wallcrossing_monotone D hrs
  · intro r s hrs
    exact xi_carath_radial_wallcrossing_index_split D hrs
  · intro ρ ε hε hgap
    calc
      xi_carath_radial_wallcrossing_radialIndex D (ρ + ε) =
          xi_carath_radial_wallcrossing_radialIndex D ρ +
            xi_carath_radial_wallcrossing_shellMultiplicity D ρ (ρ + ε) := by
          exact xi_carath_radial_wallcrossing_index_split D (le_add_of_nonneg_right hε.le)
      _ = xi_carath_radial_wallcrossing_radialIndex D ρ +
            xi_carath_radial_wallcrossing_wallMultiplicity D ρ := by
          rw [xi_carath_radial_wallcrossing_shell_eq_wall D ρ ε hε hgap]

end

end Omega.Zeta
