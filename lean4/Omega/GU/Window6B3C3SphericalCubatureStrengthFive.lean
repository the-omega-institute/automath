import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes

namespace Omega.GU

open scoped BigOperators

/-- Weights on the 21 labeled window-6 spherical support: 12 long roots, 3 negative short roots,
    3 positive short roots, and 3 boundary duplicates on the positive axes. -/
structure Window6LabeledCubatureWeights where
  longRoot : Fin 12 → ℂ
  shortNeg : Fin 3 → ℂ
  shortPos : Fin 3 → ℂ
  boundary : Fin 3 → ℂ

/-- The total mass on the positive `i`-axis after splitting it into the cyclic and boundary
    labels. -/
def axisTotal (μ : Window6LabeledCubatureWeights) (i : Fin 3) : ℂ :=
  μ.shortPos i + μ.boundary i

/-- Total mass of the labeled cubature measure. -/
noncomputable def totalMass (μ : Window6LabeledCubatureWeights) : ℂ :=
  (∑ j, μ.longRoot j) + (∑ i, μ.shortNeg i) + (∑ i, μ.shortPos i) + (∑ i, μ.boundary i)

/-- The degree-5 cubature constraints after the odd-moment and quartic-isotropy reductions:
    long roots are equal, negative-axis masses are `λ / 2`, and each positive-axis total mass is
    also `λ / 2`. -/
def IsDegreeFiveCubature (μ : Window6LabeledCubatureWeights) : Prop :=
  ∃ lam : ℂ,
    (∀ j, μ.longRoot j = lam) ∧
      (∀ i, μ.shortNeg i = lam / 2) ∧
      (∀ i, axisTotal μ i = lam / 2)

lemma totalMass_eq_fifteen_mul
    (μ : Window6LabeledCubatureWeights) (lam : ℂ) (t : Fin 3 → ℂ)
    (hlong : ∀ j, μ.longRoot j = lam)
    (hneg : ∀ i, μ.shortNeg i = lam / 2)
    (hpos : ∀ i, μ.shortPos i = lam / 2 - t i)
    (hbd : ∀ i, μ.boundary i = t i) :
    totalMass μ = 15 * lam := by
  unfold totalMass
  simp [hlong, hneg, hpos, hbd]
  ring

set_option maxHeartbeats 400000 in
/-- Paper-facing family theorem for the labeled 21-point window-6 spherical degree-5 cubatures:
    the quartic constraints force a common long-root weight `λ`, each negative-axis mass equals
    `λ / 2`, and the only remaining freedom is the three-way split of the positive-axis totals.
    thm:window6-labeled-spherical-degree5-cubature-family -/
theorem paper_window6_labeled_spherical_degree5_cubature_family
    (μ : Window6LabeledCubatureWeights) :
    IsDegreeFiveCubature μ ↔
      ∃ lam : ℂ, ∃ t : Fin 3 → ℂ,
        (∀ j, μ.longRoot j = lam) ∧
          (∀ i, μ.shortNeg i = lam / 2) ∧
          (∀ i, μ.shortPos i = lam / 2 - t i) ∧
          (∀ i, μ.boundary i = t i) ∧
          totalMass μ = 15 * lam := by
  constructor
  · rintro ⟨lam, hlong, hneg, haxis⟩
    refine ⟨lam, fun i => μ.boundary i, hlong, hneg, ?_, ?_, ?_⟩
    · intro i
      have hi := congrArg (fun z : ℂ => z - μ.boundary i) (haxis i)
      simpa [axisTotal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hi
    · intro i
      rfl
    · exact totalMass_eq_fifteen_mul μ lam (fun i => μ.boundary i) hlong hneg
        (fun i => by
          have hi := congrArg (fun z : ℂ => z - μ.boundary i) (haxis i)
          simpa [axisTotal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hi)
        (fun _ => rfl)
  · rintro ⟨lam, t, hlong, hneg, hpos, hbd, _hmass⟩
    refine ⟨lam, hlong, hneg, ?_⟩
    intro i
    unfold axisTotal
    rw [hpos i, hbd i]
    ring

end Omega.GU
