import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.POM.SufficientStatisticResidualNoninvertibility

namespace Omega.Conclusion

open Omega.POM.SufficientStatisticResidualNoninvertibility

noncomputable section

/-- The fold-`π` fiber multiplicity closed form attached to a path decomposition
`Γₓ ≃ ⨆ᵢ P_{ℓᵢ}`. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card
    (L : List ℕ) : ℕ :=
  (L.map fun ell => Nat.fib (ell + 2)).prod

/-- The inverse-substitution degree bound `∑ᵢ ⌈ℓᵢ / 2⌉`, written on naturals as
`∑ᵢ (ℓᵢ + 1) / 2`. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree
    (L : List ℕ) : ℕ :=
  (L.map fun ell => (ell + 1) / 2).sum

/-- The fold/output pair map on a fixed fiber, modeled as a constant fold label together with the
residual statistic. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map
    (L : List ℕ)
    (ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1)) :
    Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
      Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1) :=
  fun ω => (0, ℛ ω)

/-- The set of microstates that a deterministic decoder recovers correctly from the fixed fold
label and the residual statistic. -/
def conclusion_sufficient_statistic_externalization_success_collapse_successSet
    (L : List ℕ)
    (ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1))
    (δ :
      Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L)) :
    Finset (Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L)) :=
  Finset.univ.filter fun ω =>
    δ (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ ω) = ω

/-- Uniform-prior success probability for deterministic decoding from the externalized residual. -/
def conclusion_sufficient_statistic_externalization_success_collapse_successProbability
    (L : List ℕ)
    (ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1))
    (δ :
      Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L)) :
    ℝ :=
  ((conclusion_sufficient_statistic_externalization_success_collapse_successSet L ℛ δ).card : ℝ) /
    conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L

/-- Concrete fold-`π` sufficient-statistic obstruction package: the fiber multiplicity and the
inverse-substitution degree have the Fibonacci/ceiling closed forms, and any residual taking only
`deg Zₓ + 1` values forces a noninjective fold/residual pairing once the fiber is larger. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_statement : Prop :=
  ∀ L : List ℕ,
    conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L =
        (L.map fun ell => Nat.fib (ell + 2)).prod ∧
      conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L =
        (L.map fun ell => (ell + 1) / 2).sum ∧
      ∀ ℛ :
          Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
            Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1),
        conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1 <
            conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L →
          ¬ Function.Injective
            (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ)

/-- The optimal decoder can succeed on at most `d_x + 1` points of a fiber because each successful
microstate must be labeled by a distinct residual value. In the single-path case this gives the
explicit Fibonacci upper bound, and that bound collapses to `0` as the path length grows. -/
def conclusion_sufficient_statistic_externalization_success_collapse_statement : Prop :=
  (∀ L
      (ℛ :
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
          Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1))
      (δ :
        Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1) →
          Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L)),
      conclusion_sufficient_statistic_externalization_success_collapse_successProbability L ℛ δ ≤
        ((conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1 : ℕ) : ℝ) /
          conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) ∧
    (∀ ell
      (ℛ :
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card [ell]) →
          Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree [ell] + 1))
      (δ :
        Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree [ell] + 1) →
          Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card [ell])),
      conclusion_sufficient_statistic_externalization_success_collapse_successProbability [ell] ℛ
          δ ≤
        ((((ell + 1) / 2 + 1 : ℕ) : ℝ) / Nat.fib (ell + 2))) ∧
    (∀ ell,
      ((((ell + 1) / 2 + 1 : ℕ) : ℝ) / Nat.fib (ell + 2) : ℝ) ≤
        (((ell + 2 : ℕ) : ℝ) / Nat.fib (ell + 2))) ∧
    Filter.Tendsto (fun ell : ℕ => (((ell + 2 : ℕ) : ℝ) / Nat.fib (ell + 2))) Filter.atTop
      (nhds 0)

lemma conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_residual_injective_of_pair
    {L : List ℕ}
    {ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1)}
    (hinj :
      Function.Injective
        (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ)) :
    Function.Injective ℛ := by
  intro ω₁ ω₂ hω
  apply hinj
  simp [conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map, hω]

lemma conclusion_sufficient_statistic_externalization_success_collapse_success_injective
    {L : List ℕ}
    {ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1)}
    {δ :
      Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L)} :
    Function.Injective
      (fun ω :
        {ω //
          ω ∈ conclusion_sufficient_statistic_externalization_success_collapse_successSet L ℛ δ} =>
        ℛ ω.1) := by
  intro ω₁ ω₂ hω
  apply Subtype.ext
  have hω₁ :
      δ (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ ω₁.1) =
        ω₁.1 := by
    have hmem := Finset.mem_filter.mp ω₁.2
    simpa [conclusion_sufficient_statistic_externalization_success_collapse_successSet] using hmem.2
  have hω₂ :
      δ (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ ω₂.1) =
        ω₂.1 := by
    have hmem := Finset.mem_filter.mp ω₂.2
    simpa [conclusion_sufficient_statistic_externalization_success_collapse_successSet] using hmem.2
  have hpair :
      conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ ω₁.1 =
        conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ ω₂.1 := by
    simp [conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map, hω]
  calc
    ω₁.1 =
        δ (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ ω₁.1) := by
          symm
          exact hω₁
    _ = δ (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ ω₂.1) := by
          rw [hpair]
    _ = ω₂.1 := hω₂

lemma conclusion_sufficient_statistic_externalization_success_collapse_success_card_le
    (L : List ℕ)
    (ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1))
    (δ :
      Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L)) :
    (conclusion_sufficient_statistic_externalization_success_collapse_successSet L ℛ δ).card ≤
      conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1 := by
  let S := conclusion_sufficient_statistic_externalization_success_collapse_successSet L ℛ δ
  have hcard :
      Fintype.card {ω // ω ∈ S} ≤
        Fintype.card (Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1)) := by
    simpa [Fintype.card_fin] using
      Fintype.card_le_of_injective
        (fun ω :
          {ω // ω ∈ S} =>
          ℛ ω.1)
        conclusion_sufficient_statistic_externalization_success_collapse_success_injective
  simpa [S] using hcard

private lemma conclusion_sufficient_statistic_externalization_success_collapse_linear_geometric_tendsto_zero
    {r : ℝ} (hr : ‖r‖ < 1) :
    Filter.Tendsto
      (fun ell : ℕ => ((ell : ℝ) + 2) * r ^ ell)
      Filter.atTop (nhds 0) := by
  have hpowNorm :
      Summable fun ell : ℕ => ‖(((ell : ℝ) ^ 1) * r ^ ell : ℝ)‖ := by
    simpa using summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr
  have hgeomNorm :
      Summable fun ell : ℕ => ‖((r ^ ell : ℝ))‖ := by
    simpa using summable_norm_geometric_of_norm_lt_one hr
  have hpow :
      Summable fun ell : ℕ => (((ell : ℝ) ^ 1) * r ^ ell : ℝ) :=
    Summable.of_norm hpowNorm
  have hgeom :
      Summable fun ell : ℕ => ((r ^ ell : ℝ)) :=
    Summable.of_norm hgeomNorm
  have hlinear :
      Filter.Tendsto (fun ell : ℕ => (ell : ℝ) * r ^ ell) Filter.atTop (nhds 0) := by
    simpa [pow_one, Nat.cofinite_eq_atTop] using hpow.tendsto_cofinite_zero
  have htail :
      Filter.Tendsto (fun ell : ℕ => (2 : ℝ) * r ^ ell) Filter.atTop (nhds 0) := by
    simpa [Nat.cofinite_eq_atTop] using (hgeom.mul_left (2 : ℝ)).tendsto_cofinite_zero
  have hEq :
      (fun ell : ℕ => ((ell : ℝ) + 2) * r ^ ell) =ᶠ[Filter.atTop]
        fun ell : ℕ => (ell : ℝ) * r ^ ell + (2 : ℝ) * r ^ ell :=
    Filter.Eventually.of_forall fun ell => by ring
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa using hlinear.add htail

private theorem conclusion_sufficient_statistic_externalization_success_collapse_fib_lower_by_sqrt_two
    (L : ℕ) :
    (Real.sqrt 2) ^ L / Real.sqrt 2 ≤ (Nat.fib (L + 1) : ℝ) := by
  rcases Nat.even_or_odd L with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hmain : (Real.sqrt 2) ^ (2 * k) / Real.sqrt 2 ≤ (Nat.fib (2 * k + 1) : ℝ) := by
      have hnat : 2 ^ k ≤ Nat.fib (2 * k + 1) := by
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using
          Omega.fib_exponential_growth 1 k (by omega)
      have hreal : ((2 : ℝ) ^ k) ≤ (Nat.fib (2 * k + 1) : ℝ) := by
        exact_mod_cast hnat
      have hsqrt_pos : 0 < Real.sqrt 2 := by positivity
      have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := by positivity
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
      calc
        (Real.sqrt 2) ^ (2 * k) / Real.sqrt 2 = (2 : ℝ) ^ k / Real.sqrt 2 := by
          rw [pow_mul, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
        _ ≤ (2 : ℝ) ^ k := by
          exact div_le_self (by positivity) hsqrt_ge_one
        _ ≤ (Nat.fib (2 * k + 1) : ℝ) := hreal
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hmain
  · have hmain : (Real.sqrt 2) ^ (2 * k + 1) / Real.sqrt 2 ≤ (Nat.fib (2 * k + 2) : ℝ) := by
      have hnat : 2 ^ k ≤ Nat.fib (2 * k + 2) := by
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using
          Omega.fib_exponential_growth 2 k (by omega)
      have hreal : ((2 : ℝ) ^ k) ≤ (Nat.fib (2 * k + 2) : ℝ) := by
        exact_mod_cast hnat
      have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
      calc
        (Real.sqrt 2) ^ (2 * k + 1) / Real.sqrt 2 = (Real.sqrt 2) ^ (2 * k) := by
          field_simp [hsqrt_ne]
          ring
        _ = (2 : ℝ) ^ k := by
          rw [pow_mul, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
        _ ≤ (Nat.fib (2 * k + 2) : ℝ) := hreal
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hmain

/-- Paper label: `thm:conclusion-foldgauge-pi-sufficient-statistic-fiber-obstruction`. -/
theorem paper_conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction :
    conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_statement := by
  intro L
  refine ⟨rfl, rfl, ?_⟩
  intro ℛ hbig
  intro hinj
  have hresidual :
      Function.Injective ℛ :=
    conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_residual_injective_of_pair hinj
  exact
    (paper_pom_sufficient_statistic_residual_noninvertibility
      (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L) ℛ
      (by simpa using hbig)) hresidual

/-- Paper label: `thm:conclusion-sufficient-statistic-externalization-success-collapse`. -/
theorem paper_conclusion_sufficient_statistic_externalization_success_collapse :
    conclusion_sufficient_statistic_externalization_success_collapse_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L ℛ δ
    have hcard :
        (conclusion_sufficient_statistic_externalization_success_collapse_successSet L ℛ δ).card ≤
          conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1 :=
      conclusion_sufficient_statistic_externalization_success_collapse_success_card_le L ℛ δ
    have hcard_real :
        ((conclusion_sufficient_statistic_externalization_success_collapse_successSet L ℛ δ).card :
            ℝ) ≤
          (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1 : ℕ) := by
      exact_mod_cast hcard
    exact div_le_div_of_nonneg_right hcard_real (by positivity)
  · intro ell ℛ δ
    have hcard :
        (conclusion_sufficient_statistic_externalization_success_collapse_successSet [ell] ℛ δ).card ≤
          conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree [ell] + 1 :=
      conclusion_sufficient_statistic_externalization_success_collapse_success_card_le [ell] ℛ δ
    have hcard_real :
        ((conclusion_sufficient_statistic_externalization_success_collapse_successSet [ell] ℛ δ).card :
            ℝ) ≤
          (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree [ell] + 1 : ℕ) := by
      exact_mod_cast hcard
    simpa [conclusion_sufficient_statistic_externalization_success_collapse_successProbability,
      conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card,
      conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree] using
      div_le_div_of_nonneg_right hcard_real (by positivity)
  · intro ell
    have hhalf : (ell + 1) / 2 ≤ ell + 1 := Nat.div_le_self (ell + 1) 2
    have hnat : ((ell + 1) / 2 + 1 : ℕ) ≤ ell + 2 := by omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by positivity)
  · let g : ℕ → ℝ := fun ell => (((ell + 2 : ℕ) : ℝ) / Nat.fib (ell + 2))
    let h : ℕ → ℝ := fun ell => (((ell + 2 : ℕ) : ℝ) / (Real.sqrt 2) ^ ell)
    have hbound : ∀ ell, g ell ≤ h ell := by
      intro ell
      have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
      have hFib :=
        conclusion_sufficient_statistic_externalization_success_collapse_fib_lower_by_sqrt_two
          (ell + 1)
      have hFib' : (Real.sqrt 2 : ℝ) ^ ell ≤ (Nat.fib (ell + 2) : ℝ) := by
        have hEq :
            (Real.sqrt 2 : ℝ) ^ (ell + 1) / Real.sqrt 2 = (Real.sqrt 2 : ℝ) ^ ell := by
          rw [pow_succ]
          field_simp [hsqrt_ne]
        simpa [hEq, add_assoc, add_left_comm, add_comm] using hFib
      have hdiv :
          (1 : ℝ) / (Nat.fib (ell + 2) : ℝ) ≤ 1 / (Real.sqrt 2 : ℝ) ^ ell := by
        exact one_div_le_one_div_of_le (by positivity) hFib'
      have hnum_nonneg : 0 ≤ (((ell + 2 : ℕ) : ℝ)) := by positivity
      simpa [g, h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hdiv hnum_nonneg
    have hnonneg : ∀ ell, 0 ≤ g ell := by
      intro ell
      dsimp [g]
      positivity
    have hsqrt2_inv_lt_one : ‖((Real.sqrt 2 : ℝ)⁻¹)‖ < 1 := by
      have hsqrt2_pos : 0 < (Real.sqrt 2 : ℝ) := by positivity
      have hsqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
      have hval : (Real.sqrt 2 : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrt2_gt_one
      have habs : |((Real.sqrt 2 : ℝ)⁻¹)| < 1 := by
        simpa [abs_of_pos (inv_pos.mpr hsqrt2_pos)] using hval
      simpa [Real.norm_eq_abs] using habs
    have htendsto_h :
        Filter.Tendsto h Filter.atTop (nhds 0) := by
      have :=
        conclusion_sufficient_statistic_externalization_success_collapse_linear_geometric_tendsto_zero
          hsqrt2_inv_lt_one
      simpa [h, div_eq_mul_inv, Nat.cast_add, add_comm, add_left_comm, add_assoc] using this
    exact
      Omega.Entropy.tendsto_zero_of_nonneg_le_of_tendsto_zero g h hnonneg hbound htendsto_h

end

end Omega.Conclusion
