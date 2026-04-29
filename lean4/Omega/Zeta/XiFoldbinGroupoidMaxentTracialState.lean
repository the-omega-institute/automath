import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.FoldbinGroupoidTracialSimplex
import Omega.Zeta.XiFoldbinGaugeEntropyOneNatLaw

namespace Omega.Zeta

open Omega.Conclusion.FoldbinGroupoidTracialSimplex
open scoped BigOperators

/-- The KL divergence from a tracial weight on `2^m` one-dimensional blocks to the uniform
microstate pushforward. -/
noncomputable def xi_foldbin_groupoid_maxent_tracial_state_uniform_kl
    (m : ℕ) (π : Fin (2 ^ m) → ℝ) : ℝ :=
  ∑ w, π w * Real.log (π w / ((1 : ℝ) / (2 ^ m : ℝ)))

/-- The canonical tracial state on the `2^m` one-dimensional block decomposition: the escort
weights for the constant multiplicity function `d ≡ 1`, hence the uniform law on the blocks. -/
noncomputable def xi_foldbin_groupoid_maxent_tracial_state_uniform_weight
    (m : ℕ) : Fin (2 ^ m) → ℝ :=
  escortWeight (ι := Fin (2 ^ m)) (fun _ => 1)

/-- The simplex package identifies tracial states with block weights; for the constant
multiplicity profile `d ≡ 1`, the canonical tracial state has zero KL gap to the uniform
microstate pushforward and achieves entropy `m log 2`. -/
def xi_foldbin_groupoid_maxent_tracial_state_statement (m : ℕ) : Prop :=
  let simplex := tracialSimplex (ι := Fin (2 ^ m))
  let τ := xi_foldbin_groupoid_maxent_tracial_state_uniform_weight m
  τ ∈ simplex ∧
    (∀ σ, σ ∈ simplex →
      ∃! α : Fin (2 ^ m) → ℝ,
        (∀ w, 0 ≤ α w) ∧
          Finset.univ.sum α = 1 ∧
          σ = fun u => ∑ w, α w * normalizedBlockTrace w u) ∧
    xi_foldbin_groupoid_maxent_tracial_state_uniform_kl m τ = 0 ∧
    (-(∑ w, τ w * Real.log (τ w))) = (m : ℝ) * Real.log 2

/-- Paper label: `thm:xi-foldbin-groupoid-maxent-tracial-state`. The existing tracial-simplex
package identifies tracial states with simplex weights on the Wedderburn blocks. For the constant
block-size profile `d ≡ 1`, the escort weight is the uniform law on the `2^m` blocks, so its KL
gap to the uniform microstate pushforward vanishes and its entropy is exactly `m log 2`. -/
theorem paper_xi_foldbin_groupoid_maxent_tracial_state
    (m : ℕ) : xi_foldbin_groupoid_maxent_tracial_state_statement m := by
  let d : Fin (2 ^ m) → ℕ := fun _ => 1
  let τ := xi_foldbin_groupoid_maxent_tracial_state_uniform_weight m
  have hd : ∀ w : Fin (2 ^ m), 0 < d w := by
    intro w
    simp [d]
  have hpack :=
    paper_conclusion_foldbin_groupoid_tracial_simplex_package (ι := Fin (2 ^ m)) d hd
  have hτ_mem : τ ∈ tracialSimplex (ι := Fin (2 ^ m)) := by
    simpa [d, xi_foldbin_groupoid_maxent_tracial_state_uniform_weight, τ] using hpack.2
  have hτ_sum : Finset.univ.sum τ = 1 := hτ_mem.2
  have hτ_uniform : ∀ w : Fin (2 ^ m), τ w = (1 : ℝ) / (2 ^ m : ℝ) := by
    intro w
    simp [τ, xi_foldbin_groupoid_maxent_tracial_state_uniform_weight, escortWeight]
  have hτ_pos : ∀ w : Fin (2 ^ m), 0 < τ w := by
    intro w
    rw [hτ_uniform w]
    positivity
  have hkl_zero :
      xi_foldbin_groupoid_maxent_tracial_state_uniform_kl m τ = 0 := by
    unfold xi_foldbin_groupoid_maxent_tracial_state_uniform_kl
    simp [hτ_uniform]
  have hentropy :
      (-(∑ w, τ w * Real.log (τ w))) = (m : ℝ) * Real.log 2 := by
    have hEntropyLaw :=
      paper_xi_foldbin_gauge_entropy_one_nat_law (X := Fin (2 ^ m)) m τ (fun _ => (1 : ℝ))
        hτ_uniform hτ_sum hτ_pos
    have hzero : (m : ℝ) * Real.log 2 - (-(∑ w, τ w * Real.log (τ w))) = 0 := by
      simpa using hEntropyLaw.symm
    have hzero' : -(∑ w, τ w * Real.log (τ w)) - (m : ℝ) * Real.log 2 = 0 := by
      linarith
    exact sub_eq_zero.mp hzero'
  refine ⟨hτ_mem, ?_, hkl_zero, hentropy⟩
  intro σ hσ
  simpa using hpack.1 σ hσ

end Omega.Zeta
