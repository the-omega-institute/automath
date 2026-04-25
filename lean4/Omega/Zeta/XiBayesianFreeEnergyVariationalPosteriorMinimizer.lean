import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Tactic

namespace Omega.Zeta

open BigOperators
open InformationTheory

noncomputable section

/-- Paper label: `thm:xi-bayesian-free-energy-variational-posterior-minimizer`. -/
theorem paper_xi_bayesian_free_energy_variational_posterior_minimizer {ι : Type*} [Fintype ι]
    [DecidableEq ι] (w μ π : ι → ℝ) (Z : ℝ) (hw_pos : ∀ i, 0 < w i)
    (hμ_pos : ∀ i, 0 < μ i) (hZ_pos : 0 < Z) (hZ : Z = ∑ i, w i * μ i)
    (hπ : ∀ i, π i = w i * μ i / Z) :
    let objective : (ι → ℝ) → ℝ := fun q =>
      (∑ i, q i * (-Real.log (μ i))) + (∑ i, q i * Real.log (q i / w i));
    (∀ q : ι → ℝ, (∀ i, 0 < q i) → (∑ i, q i = 1) → -Real.log Z ≤ objective q) ∧
      objective π = -Real.log Z ∧
        (∀ q : ι → ℝ, (∀ i, 0 < q i) → (∑ i, q i = 1) →
          objective q = -Real.log Z → q = π) := by
  classical
  dsimp only
  let objective : (ι → ℝ) → ℝ := fun q =>
    (∑ i, q i * (-Real.log (μ i))) + (∑ i, q i * Real.log (q i / w i))
  have hπ_pos : ∀ i, 0 < π i := by
    intro i
    rw [hπ i]
    exact div_pos (mul_pos (hw_pos i) (hμ_pos i)) hZ_pos
  have hπ_sum : ∑ i, π i = 1 := by
    calc
      ∑ i, π i = ∑ i, w i * μ i / Z := by
        exact Finset.sum_congr rfl (fun i _ => hπ i)
      _ = (∑ i, w i * μ i) / Z := by
        rw [Finset.sum_div]
      _ = Z / Z := by
        rw [← hZ]
      _ = 1 := by
        exact div_self (ne_of_gt hZ_pos)
  have hlog_ratio :
      ∀ (q : ι → ℝ), (∀ i, 0 < q i) → ∀ i,
        Real.log (q i / π i) =
          Real.log (q i / w i) - Real.log (μ i) + Real.log Z := by
    intro q hq_pos i
    have hq_ne : q i ≠ 0 := ne_of_gt (hq_pos i)
    have hw_ne : w i ≠ 0 := ne_of_gt (hw_pos i)
    have hμ_ne : μ i ≠ 0 := ne_of_gt (hμ_pos i)
    have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
    have hqw_pos : 0 < q i / w i := div_pos (hq_pos i) (hw_pos i)
    have hZμ_pos : 0 < Z / μ i := div_pos hZ_pos (hμ_pos i)
    calc
      Real.log (q i / π i) =
          Real.log ((q i / w i) * (Z / μ i)) := by
        rw [hπ i]
        congr 1
        field_simp [hq_ne, hw_ne, hμ_ne, hZ_ne]
      _ = Real.log (q i / w i) + Real.log (Z / μ i) := by
        rw [Real.log_mul (ne_of_gt hqw_pos) (ne_of_gt hZμ_pos)]
      _ = Real.log (q i / w i) + (Real.log Z - Real.log (μ i)) := by
        rw [Real.log_div hZ_ne hμ_ne]
      _ = Real.log (q i / w i) - Real.log (μ i) + Real.log Z := by
        ring
  have hobjective_kl :
      ∀ (q : ι → ℝ), (∀ i, 0 < q i) → (∑ i, q i = 1) →
        objective q + Real.log Z = ∑ i, q i * Real.log (q i / π i) := by
    intro q hq_pos hq_sum
    have hlogZ_sum : Real.log Z = ∑ i, q i * Real.log Z := by
      rw [← Finset.sum_mul, hq_sum, one_mul]
    calc
      objective q + Real.log Z =
          (∑ i, q i * (-Real.log (μ i))) +
            (∑ i, q i * Real.log (q i / w i)) + ∑ i, q i * Real.log Z := by
        nth_rewrite 1 [hlogZ_sum]
        ring
      _ = ∑ i, (q i * (-Real.log (μ i)) +
          q i * Real.log (q i / w i) + q i * Real.log Z) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ = ∑ i, q i * Real.log (q i / π i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hlog_ratio q hq_pos i]
        ring
  have hklfun_sum :
      ∀ (q : ι → ℝ), (∀ i, 0 < q i) → (∑ i, q i = 1) →
        (∑ i, q i * Real.log (q i / π i)) =
          ∑ i, π i * klFun (q i / π i) := by
    intro q hq_pos hq_sum
    have hterm : ∀ i, π i * klFun (q i / π i) =
        q i * Real.log (q i / π i) + π i - q i := by
      intro i
      rw [klFun_apply]
      have hπ_ne : π i ≠ 0 := ne_of_gt (hπ_pos i)
      field_simp [hπ_ne]
    calc
      ∑ i, q i * Real.log (q i / π i) =
          ∑ i, (q i * Real.log (q i / π i) + π i - q i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hπ_sum, hq_sum]
        ring
      _ = ∑ i, π i * klFun (q i / π i) := by
        exact Finset.sum_congr rfl (fun i _ => (hterm i).symm)
  have hkl_nonneg :
      ∀ (q : ι → ℝ), (∀ i, 0 < q i) → 0 ≤ ∑ i, π i * klFun (q i / π i) := by
    intro q hq_pos
    refine Finset.sum_nonneg ?_
    intro i _
    exact mul_nonneg (le_of_lt (hπ_pos i))
      (klFun_nonneg (le_of_lt (div_pos (hq_pos i) (hπ_pos i))))
  refine ⟨?_, ?_, ?_⟩
  · intro q hq_pos hq_sum
    have hrew := hobjective_kl q hq_pos hq_sum
    have hklrew := hklfun_sum q hq_pos hq_sum
    have hnonneg : 0 ≤ objective q + Real.log Z := by
      rw [hrew, hklrew]
      exact hkl_nonneg q hq_pos
    linarith
  · have hπ_objective : objective π + Real.log Z = ∑ i, π i * Real.log (π i / π i) :=
      hobjective_kl π hπ_pos hπ_sum
    have hsum_zero : (∑ i, π i * Real.log (π i / π i)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [div_self (ne_of_gt (hπ_pos i)), Real.log_one, mul_zero]
    linarith
  · intro q hq_pos hq_sum hq_obj
    have hrew := hobjective_kl q hq_pos hq_sum
    have hklrew := hklfun_sum q hq_pos hq_sum
    have hsum_zero : (∑ i, π i * klFun (q i / π i)) = 0 := by
      linarith
    funext i
    have hterm_nonneg :
        ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ π j * klFun (q j / π j) := by
      intro j _
      exact mul_nonneg (le_of_lt (hπ_pos j))
        (klFun_nonneg (le_of_lt (div_pos (hq_pos j) (hπ_pos j))))
    have hterm_zero : π i * klFun (q i / π i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_zero i (Finset.mem_univ i)
    have hkl_zero : klFun (q i / π i) = 0 := by
      exact (mul_eq_zero.mp hterm_zero).resolve_left (ne_of_gt (hπ_pos i))
    have hratio_one : q i / π i = 1 :=
      (klFun_eq_zero_iff (le_of_lt (div_pos (hq_pos i) (hπ_pos i)))).mp hkl_zero
    have hπ_ne : π i ≠ 0 := ne_of_gt (hπ_pos i)
    field_simp [hπ_ne] at hratio_one
    exact hratio_one

end

end Omega.Zeta
