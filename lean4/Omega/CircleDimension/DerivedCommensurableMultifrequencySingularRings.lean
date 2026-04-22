import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- Concrete multifrequency Laurent data together with a polynomial factorization witness for the
derivative after clearing negative powers. -/
structure derived_commensurable_multifrequency_singular_rings_data where
  ι : Type*
  instFintypeι : Fintype ι
  coeff : ι → ℂ
  frequency : ι → ℕ
  q : ℤ
  g : ℕ
  hg_pos : 0 < g
  L : ℕ
  r : ℕ
  hr_lt : r < g
  Q : Polynomial ℂ
  hQ_ne : Q ≠ 0
  factorization :
    ∀ w : ℂ, w ≠ 0 →
      (w ^ L) *
          (∑ j : ι,
            coeff j *
              ((((q + (frequency j : ℤ)) : ℂ) * w ^ (q + (frequency j : ℤ) - 1)) +
                (((q - (frequency j : ℤ)) : ℂ) * w ^ (q - (frequency j : ℤ) - 1)))) =
        w ^ r * Q.eval (w ^ g)

attribute [instance] derived_commensurable_multifrequency_singular_rings_data.instFintypeι

noncomputable def derived_commensurable_multifrequency_singular_rings_laurent_derivative
    (D : derived_commensurable_multifrequency_singular_rings_data) (w : ℂ) : ℂ :=
  ∑ j : D.ι,
    D.coeff j *
      ((((D.q + (D.frequency j : ℤ)) : ℂ) * w ^ (D.q + (D.frequency j : ℤ) - 1)) +
        (((D.q - (D.frequency j : ℤ)) : ℂ) * w ^ (D.q - (D.frequency j : ℤ) - 1)))

noncomputable def derived_commensurable_multifrequency_singular_rings_root_radii
    (D : derived_commensurable_multifrequency_singular_rings_data) : Finset ℝ :=
  D.Q.roots.toFinset.image fun z => ‖z‖

def derived_commensurable_multifrequency_singular_rings_spec
    (D : derived_commensurable_multifrequency_singular_rings_data) : Prop :=
  (∀ w : ℂ, w ≠ 0 →
    (w ^ D.L) * derived_commensurable_multifrequency_singular_rings_laurent_derivative D w =
      w ^ D.r * D.Q.eval (w ^ D.g)) ∧
    (∀ w : ℂ, w ≠ 0 →
      derived_commensurable_multifrequency_singular_rings_laurent_derivative D w = 0 →
        ‖w ^ D.g‖ ∈
          derived_commensurable_multifrequency_singular_rings_root_radii D) ∧
    Set.Finite
      {ρ : ℝ | ∃ w : ℂ, w ≠ 0 ∧
          derived_commensurable_multifrequency_singular_rings_laurent_derivative D w = 0 ∧
            ‖w ^ D.g‖ = ρ}

/-- A factorization of the cleared Laurent derivative through `Q(w^g)` forces the set of
`g`-power singular radii to be finite, with witnesses coming from the finitely many roots of `Q`.
    thm:derived-commensurable-multifrequency-singular-rings -/
theorem paper_derived_commensurable_multifrequency_singular_rings
    (D : derived_commensurable_multifrequency_singular_rings_data) :
    derived_commensurable_multifrequency_singular_rings_spec D := by
  classical
  have hfactor :
      ∀ w : ℂ, w ≠ 0 →
        (w ^ D.L) * derived_commensurable_multifrequency_singular_rings_laurent_derivative D w =
          w ^ D.r * D.Q.eval (w ^ D.g) := by
    intro w hw
    simpa [derived_commensurable_multifrequency_singular_rings_laurent_derivative] using
      D.factorization w hw
  have hcontain :
      ∀ w : ℂ, w ≠ 0 →
        derived_commensurable_multifrequency_singular_rings_laurent_derivative D w = 0 →
          ‖w ^ D.g‖ ∈
            derived_commensurable_multifrequency_singular_rings_root_radii D := by
    intro w hw hderiv
    have hfac :
        (w ^ D.L) * derived_commensurable_multifrequency_singular_rings_laurent_derivative D w =
          w ^ D.r * D.Q.eval (w ^ D.g) := by
      exact hfactor w hw
    have hprod : w ^ D.r * D.Q.eval (w ^ D.g) = 0 := by
      simpa [hderiv] using hfac
    have hwr_ne : w ^ D.r ≠ 0 := by
      exact pow_ne_zero _ hw
    have hroot_eval : D.Q.eval (w ^ D.g) = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_left hwr_ne
    have hroot : w ^ D.g ∈ D.Q.roots := by
      rw [Polynomial.mem_roots D.hQ_ne]
      exact hroot_eval
    refine Finset.mem_image.mpr ?_
    exact ⟨w ^ D.g, by simpa using hroot, rfl⟩
  refine ⟨hfactor, hcontain, ?_⟩
  ·
    refine Set.Finite.subset (derived_commensurable_multifrequency_singular_rings_root_radii D).finite_toSet ?_
    intro ρ hρ
    rcases hρ with ⟨w, hw, hderiv, rfl⟩
    exact hcontain w hw hderiv

end

end Omega.CircleDimension
