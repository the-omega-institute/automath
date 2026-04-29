import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The boundary integral of a `(k - 1)`-cochain over the `2k` oriented codimension-one faces of a
`k`-cell in a finite cubical model. -/
def pom_cubical_stokes_energy_sampling_boundaryIntegral {α : Type*} {N k : ℕ}
    (faces : Fin N → Fin (2 * k) → α)
    (sgn : Fin N → Fin (2 * k) → ℝ)
    (ω : α → ℝ) (σ : Fin N) : ℝ :=
  ∑ j : Fin (2 * k), sgn σ j * ω (faces σ j)

/-- The audited `ℓ²` energy is the finite sum of squared boundary integrals over the `k`-cells. -/
def pom_cubical_stokes_energy_sampling_energy {α : Type*} {N k : ℕ}
    (faces : Fin N → Fin (2 * k) → α)
    (sgn : Fin N → Fin (2 * k) → ℝ)
    (ω : α → ℝ) : ℝ :=
  ∑ σ : Fin N, (pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ) ^ 2

/-- The universal Hoeffding right-hand side for square-valued samples bounded by `4 k²`. -/
def pom_cubical_stokes_energy_sampling_hoeffdingRhs (k : ℕ) (M ε : ℝ) : ℝ :=
  2 * Real.exp (-(2 * M * ε ^ 2) / (4 * (k : ℝ) ^ 2) ^ 2)

/-- Paper label: `thm:pom-cubical-stokes-energy-sampling`.
Unfolding the cubical coboundary gives the exact energy identity, each square sample is bounded by
`4 k²` when the cochain has unit sup-norm on faces, and the usual sample-size threshold forces the
Hoeffding tail bound below `δ`. -/
theorem paper_pom_cubical_stokes_energy_sampling {α : Type*} {N k : ℕ}
    (hk : 1 ≤ k)
    (faces : Fin N → Fin (2 * k) → α)
    (sgn : Fin N → Fin (2 * k) → ℝ)
    (ω : α → ℝ)
    (hsgn : ∀ σ j, |sgn σ j| = 1)
    (hω : ∀ τ, |ω τ| ≤ 1) :
    pom_cubical_stokes_energy_sampling_energy faces sgn ω =
      ∑ σ : Fin N, (pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ) ^ 2 ∧
    (∀ σ : Fin N,
      |pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ| ≤ 2 * k ∧
        0 ≤ (pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ) ^ 2 ∧
        (pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ) ^ 2 ≤
          4 * (k : ℝ) ^ 2) ∧
    (∀ {ε δ M : ℝ}, 0 < ε → 0 < δ → δ ≤ 2 →
      8 * (k : ℝ) ^ 4 * Real.log (2 / δ) ≤ M * ε ^ 2 →
      pom_cubical_stokes_energy_sampling_hoeffdingRhs k M ε ≤ δ) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro σ
    have habs :
        |pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ| ≤ 2 * k := by
      unfold pom_cubical_stokes_energy_sampling_boundaryIntegral
      calc
        |∑ j : Fin (2 * k), sgn σ j * ω (faces σ j)|
            ≤ ∑ j : Fin (2 * k), |sgn σ j * ω (faces σ j)| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (s := (Finset.univ : Finset (Fin (2 * k))))
                    (f := fun j : Fin (2 * k) => sgn σ j * ω (faces σ j)))
        _ ≤ ∑ _j : Fin (2 * k), (1 : ℝ) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              calc
                |sgn σ j * ω (faces σ j)| = |ω (faces σ j)| := by
                  rw [abs_mul, hsgn σ j, one_mul]
                _ ≤ 1 := hω (faces σ j)
        _ = 2 * k := by simp
    have hsq_nonneg :
        0 ≤ (pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ) ^ 2 := by
      positivity
    have hsq_le :
        (pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ) ^ 2 ≤
          (2 * (k : ℝ)) ^ 2 := by
      have hneg :
          -(2 * (k : ℝ)) ≤ pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ :=
        (abs_le.mp habs).1
      have hpos :
          pom_cubical_stokes_energy_sampling_boundaryIntegral faces sgn ω σ ≤ 2 * (k : ℝ) :=
        (abs_le.mp habs).2
      nlinarith
    refine ⟨habs, hsq_nonneg, ?_⟩
    nlinarith [hsq_le]
  · intro ε δ M hε hδ hδ_le hM
    have hk_real : 0 < (k : ℝ) := by exact_mod_cast hk
    have hk4_pos : 0 < 8 * (k : ℝ) ^ 4 := by positivity
    have hratio_pos : 0 < 2 / δ := by positivity
    have hlog_le : Real.log (2 / δ) ≤ (M * ε ^ 2) / (8 * (k : ℝ) ^ 4) := by
      refine (le_div_iff₀ hk4_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hM
    have hexponent_le :
        -(M * ε ^ 2 / (8 * (k : ℝ) ^ 4)) ≤ -Real.log (2 / δ) := by
      linarith
    have hpow_ne : (8 * (k : ℝ) ^ 4) ≠ 0 := by positivity
    have hexponent_eq :
        -(2 * M * ε ^ 2) / (4 * (k : ℝ) ^ 2) ^ 2 = -(M * ε ^ 2 / (8 * (k : ℝ) ^ 4)) := by
      field_simp [hpow_ne, hk_real.ne']
      ring
    have hexp_le :
        Real.exp (-(2 * M * ε ^ 2) / (4 * (k : ℝ) ^ 2) ^ 2) ≤
          Real.exp (-Real.log (2 / δ)) := by
      rw [hexponent_eq]
      exact Real.exp_le_exp.mpr hexponent_le
    have hlog_exp : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
      rw [Real.exp_neg, Real.exp_log hratio_pos]
      field_simp [hδ.ne']
    unfold pom_cubical_stokes_energy_sampling_hoeffdingRhs
    calc
      2 * Real.exp (-(2 * M * ε ^ 2) / (4 * (k : ℝ) ^ 2) ^ 2)
          ≤ 2 * Real.exp (-Real.log (2 / δ)) := by gcongr
      _ = δ := by rw [hlog_exp]; ring

end

end Omega.POM
