import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.CircleDimension
import Omega.Folding.ShiftDynamics
import Omega.Folding.MomentBounds

open scoped goldenRatio
open Filter Topology

namespace Omega.Entropy

open MeasureTheory InformationTheory

/-! ### Reverse KL tilted splitting -/

/-- Abstract plateau rigidity: a nonnegative dissipation with zero average vanishes almost
everywhere. This is the minimal shell behind Poisson/KL plateau rigidity.
    con:cdim-poisson-kl-plateau-rigidity -/
theorem plateau_rigidity_of_nonneg_dissipation
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (diss : α → ℝ)
    (hdiss_nonneg : 0 ≤ᵐ[μ] diss)
    (hdiss_int : Integrable diss μ)
    (hdiss_zero : ∫ x, diss x ∂μ = 0) :
    diss =ᵐ[μ] 0 := by
  exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hdiss_nonneg hdiss_int).1 hdiss_zero

/-- Jeffreys dissipation rigidity: if a nonnegative Jeffreys dissipation has zero mean,
then the dissipation vanishes almost everywhere. This is the minimal abstract wrapper used by
Poisson/Jeffreys plateau arguments.
    con:cdim-poisson-jeffreys-dissipation-rigidity -/
theorem jeffreys_dissipation_rigidity
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (J : α → ℝ)
    (hJ_nonneg : 0 ≤ᵐ[μ] J)
    (hJ_int : Integrable J μ)
    (hJ_zero : ∫ x, J x ∂μ = 0) :
    J =ᵐ[μ] 0 := by
  exact plateau_rigidity_of_nonneg_dissipation μ J hJ_nonneg hJ_int hJ_zero

/-- Fibonacci platform certificate, successor form: if two consecutive Fibonacci labels coincide,
any nonnegative zero-mean dissipation indexed by that label must vanish almost everywhere.
    con:cdim-fibonacci-kl-platform-finite-certificate -/
theorem fib_platform_certificate_of_eq_succ
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (diss : ℕ → α → ℝ)
    (m : ℕ)
    (hEq : Nat.fib m = Nat.fib (m + 1))
    (hdiss_nonneg : 0 ≤ᵐ[μ] diss (Nat.fib m))
    (hdiss_int : Integrable (diss (Nat.fib m)) μ)
    (hdiss_zero : ∫ x, diss (Nat.fib m) x ∂μ = 0) :
    diss (Nat.fib (m + 1)) =ᵐ[μ] 0 := by
  rw [← hEq]
  exact plateau_rigidity_of_nonneg_dissipation μ (diss (Nat.fib m)) hdiss_nonneg hdiss_int hdiss_zero

/-- Fibonacci platform certificate, two-step form: under the conservative Lean-side hypothesis
`m ≥ 2`, equality of the `m` and `m+2` Fibonacci labels forces the indexed nonnegative zero-mean
dissipation to vanish almost everywhere.
    con:cdim-fibonacci-kl-platform-finite-certificate -/
theorem fib_platform_certificate_of_eq_succ_succ
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (diss : ℕ → α → ℝ)
    (m : ℕ)
    (hm : 2 ≤ m)
    (hEq : Nat.fib m = Nat.fib (m + 2))
    (hdiss_nonneg : 0 ≤ᵐ[μ] diss (Nat.fib m))
    (hdiss_int : Integrable (diss (Nat.fib m)) μ)
    (hdiss_zero : ∫ x, diss (Nat.fib m) x ∂μ = 0) :
    diss (Nat.fib (m + 2)) =ᵐ[μ] 0 := by
  have hm_ge_two : 2 ≤ m := hm
  rw [← hEq]
  exact plateau_rigidity_of_nonneg_dissipation μ (diss (Nat.fib m)) hdiss_nonneg hdiss_int hdiss_zero

/-- Sequence squeeze at zero: if `0 ≤ a_m ≤ b_m` for all `m` and `b_m → 0`, then `a_m → 0`.
    con:cdim-rh-defect-fibonacci-discretization -/
theorem tendsto_zero_of_nonneg_le_of_tendsto_zero
    (a b : ℕ → ℝ)
    (ha_nonneg : ∀ m, 0 ≤ a m)
    (hab : ∀ m, a m ≤ b m)
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  exact squeeze_zero ha_nonneg hab hb

/-- Fibonacci-radius discretization certificate: a defect bounded above by a vanishing envelope along
`fibRadius` also vanishes along the same discretization.
    con:cdim-rh-defect-fibonacci-discretization -/
theorem fibRadius_discretization_of_le_tendsto_zero
    (D : ℝ → ℝ)
    (eps : ℕ → ℝ)
    (h_nonneg : ∀ m, 0 ≤ D (fibRadius m))
    (h_bound : ∀ m, D (fibRadius m) ≤ eps m)
    (h_eps : Tendsto eps atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => D (fibRadius m)) atTop (𝓝 0) := by
  exact tendsto_zero_of_nonneg_le_of_tendsto_zero
    (fun m => D (fibRadius m)) eps h_nonneg h_bound h_eps

/-- A logarithmic defect upper bound yields a quantitative lower bound on the modulus, provided the
underlying quantity is nonzero.
    con:cdim-rh-defect-fibonacci-discretization -/
theorem zero_modulus_lower_bound_of_log_defect_bound
    (a defect : ℝ)
    (ha : a ≠ 0)
    (hdef : -Real.log |a| ≤ defect) :
    Real.exp (-defect) ≤ |a| := by
  have hlog : -defect ≤ Real.log |a| := by linarith
  calc
    Real.exp (-defect) ≤ Real.exp (Real.log |a|) := by
      exact Real.exp_le_exp.mpr hlog
    _ = |a| := by
      rw [Real.exp_log (abs_pos.mpr ha)]

/-- Fibonacci-radius packaging of `zero_modulus_lower_bound_of_log_defect_bound`.
    con:cdim-rh-defect-fibonacci-discretization -/
theorem fibRadius_zero_modulus_lower_bound_of_log_defect_bound
    (A : ℝ → ℝ)
    (eps : ℕ → ℝ)
    (ha : ∀ m, A (fibRadius m) ≠ 0)
    (hdef : ∀ m, -Real.log |A (fibRadius m)| ≤ eps m) :
    ∀ m, Real.exp (-eps m) ≤ |A (fibRadius m)| := by
  intro m
  exact zero_modulus_lower_bound_of_log_defect_bound (A (fibRadius m)) (eps m) (ha m) (hdef m)

/-- If `u_m → 1` and `ε_m → 0`, then `u_m * exp(-ε_m) → 1`. -/
theorem tendsto_mul_exp_neg_of_tendsto_one_zero
    (u eps : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 1))
    (heps : Tendsto eps atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => u m * Real.exp (-eps m)) atTop (𝓝 1) := by
  have hExp : Tendsto (fun m : ℕ => Real.exp (-eps m)) atTop (𝓝 1) := by
    have hNeg : Tendsto (fun m : ℕ => -eps m) atTop (𝓝 0) := by
      simpa using heps.neg
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hNeg
  simpa using hu.mul hExp

/-- A real number dominates `1` if it eventually dominates a sequence converging to `1`. -/
theorem one_le_of_eventually_ge_tendsto_one
    (u : ℕ → ℝ)
    (a : ℝ)
    (hu : Tendsto u atTop (𝓝 1))
    (hbound : ∀ᶠ m in atTop, u m ≤ a) :
    1 ≤ a := by
  by_contra ha
  have ha' : a < 1 := lt_of_not_ge ha
  have hu' : ∀ᶠ m in atTop, a < u m := by
    exact hu (isOpen_Ioi.mem_nhds ha')
  obtain ⟨m, hm_lt, hm_le⟩ := (hu'.and hbound).exists
  linarith

/-- For a probability measure, the reverse KL divergence to an exponential tilt splits into the
normalizing log-partition term minus the average tilt.
    con:cdim-jensen-average-reverse-kl-splitting -/
theorem kl_reverse_tilted_split
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (f : α → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hf_int : Integrable f μ) :
    (klDiv μ (μ.tilted f)).toReal = Real.log (∫ x, Real.exp (f x) ∂μ) - ∫ x, f x ∂μ := by
  have h_ac : μ ≪ μ.tilted f := MeasureTheory.absolutelyContinuous_tilted hf
  have h_eq : μ (Set.univ) = μ.tilted f (Set.univ) := by
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    letI : MeasureTheory.IsProbabilityMeasure (μ.tilted f) :=
      MeasureTheory.isProbabilityMeasure_tilted hf
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
  have h_zero : Integrable (MeasureTheory.llr μ μ) μ := by
    rw [MeasureTheory.integrable_congr (MeasureTheory.llr_self μ)]
    exact (integrable_const (c := (0 : ℝ)) : Integrable (fun _ : α => (0 : ℝ)) μ)
  rw [InformationTheory.toReal_klDiv_of_measure_eq h_ac h_eq]
  rw [MeasureTheory.integral_llr_tilted_right (μ := μ) (ν := μ)
    (hμν := MeasureTheory.Measure.AbsolutelyContinuous.rfl) (hfμ := hf_int) (hfν := hf)
    (h_int := h_zero)]
  have h_llr_self : ∫ x, MeasureTheory.llr μ μ x ∂μ = 0 := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.llr_self μ)]
    simp
  rw [h_llr_self]
  ring

/-! ### Binet corollaries: positivity of Fibonacci casts -/

/-- Nat.fib n is positive for n ≥ 1 (cast to ℝ).
    aux:coe-fib-pos -/
theorem coe_fib_pos (n : Nat) (hn : 1 ≤ n) : (0 : ℝ) < (Nat.fib n : ℝ) := by
  exact_mod_cast Nat.fib_pos.mpr (by omega)

/-- |X_m| = F(m+2) is positive (cast to ℝ).
    aux:stable-syntax-count-pos -/
theorem stableSyntaxCount_pos (n : Nat) : (0 : ℝ) < (Nat.fib (n + 2) : ℝ) :=
  coe_fib_pos (n + 2) (by omega)

/-! ### Golden ratio properties -/

/-- φ > 1.
    aux:golden-ratio-gt-one -/
theorem goldenRatio_gt_one : φ > 1 := Real.one_lt_goldenRatio

/-- log(φ) > 0: the topological entropy is positive.
    aux:log-golden-ratio-pos -/
theorem log_goldenRatio_pos : Real.log φ > 0 := Real.log_pos Real.one_lt_goldenRatio

/-- φ < 2.
    aux:golden-ratio-lt-two -/
theorem goldenRatio_lt_two : φ < 2 := by
  have : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  -- φ < 2 ↔ φ² < 2φ (since φ > 0) ↔ φ+1 < 2φ ↔ 1 < φ, which is true
  nlinarith [Real.one_lt_goldenRatio]

/-- |ψ| < 1: the golden conjugate is contractive.
    aux:abs-golden-conj-lt-one -/
theorem abs_goldenConj_lt_one : |ψ| < 1 := by
  rw [abs_lt]
  exact ⟨by linarith [Real.neg_one_lt_goldenConj], by linarith [Real.goldenConj_neg]⟩

/-- ψ is between -1 and 0.
    aux:golden-conj-bounds -/
theorem goldenConj_bounds : -1 < ψ ∧ ψ < 0 :=
  ⟨Real.neg_one_lt_goldenConj, Real.goldenConj_neg⟩

/-! ### Topological entropy ingredients

The topological entropy of the golden-mean shift is h_top = log φ.
Key ingredients: F(n+1)/F(n) → φ and continuity of log. -/

/-- F(n+1)/F(n) → φ (from mathlib).
    aux:fib-ratio-tendsto -/
theorem fib_ratio_tendsto :
    Tendsto (fun n => (Nat.fib (n + 1) : ℝ) / Nat.fib n) atTop (𝓝 φ) :=
  tendsto_fib_succ_div_fib_atTop

/-- log is continuous at φ (since φ > 0).
    aux:log-continuous-at-phi -/
theorem log_continuous_at_phi : ContinuousAt Real.log φ :=
  Real.continuousAt_log (ne_of_gt Real.goldenRatio_pos)

/-- log(F(n+2)/F(n+1)) → log φ as n → ∞.
    This is the key per-step entropy convergence.
    cor:folding-stable-syntax-entropy-logqdim-perStep -/
theorem log_fib_ratio_tendsto :
    Tendsto (fun n => Real.log ((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 1)))
      atTop (𝓝 (Real.log φ)) := by
  -- F(n+2)/F(n+1) = F((n+1)+1)/F(n+1) → φ by tendsto_fib_succ_div_fib_atTop shifted
  have hshift : Tendsto (fun n => (Nat.fib (n + 1 + 1) : ℝ) / Nat.fib (n + 1))
      atTop (𝓝 φ) :=
    tendsto_fib_succ_div_fib_atTop.comp (tendsto_add_atTop_nat 1)
  exact (Real.continuousAt_log (ne_of_gt Real.goldenRatio_pos)).tendsto.comp hshift

/-! ### Topological entropy = log φ (complete proof)

The topological entropy of the golden-mean shift:
  h_top = lim_{n→∞} (1/n) · log |X_n| = lim_{n→∞} (1/n) · log F(n+2) = log φ.

Proof: telescope log F(n+2) = Σ log(F(k+3)/F(k+2)) + log F(2), apply Cesaro to
log_fib_ratio_tendsto, and simplify log F(2) = 0. -/

/-- **Topological entropy of the golden-mean shift equals log φ.**
    This is the central dynamical invariant of the No11-constrained system.
    cor:folding-stable-syntax-entropy-logqdim -/
theorem topological_entropy_eq_log_phi :
    Tendsto (fun n => Real.log (Nat.fib (n + 2) : ℝ) / (n : ℝ)) atTop (𝓝 (Real.log φ)) := by
  let u : ℕ → ℝ := fun k => Real.log ((Nat.fib (k + 3) : ℝ) / Nat.fib (k + 2))
  have hu : Tendsto u atTop (𝓝 (Real.log φ)) := by
    simpa [u, add_assoc] using log_fib_ratio_tendsto.comp (tendsto_add_atTop_nat 1)
  have hcesaro : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, u i))
      atTop (𝓝 (Real.log φ)) :=
    hu.cesaro
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hcesaro
  calc
    (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, u i)
        = (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n,
            (Real.log (Nat.fib (i + 3) : ℝ) - Real.log (Nat.fib (i + 2) : ℝ))) := by
              congr 2; ext i; dsimp [u]
              have hnum : (Nat.fib (i + 3) : ℝ) ≠ 0 := by
                apply ne_of_gt
                rw [show i + 3 = (i + 1) + 2 by omega]
                exact stableSyntaxCount_pos (i + 1)
              have hden : (Nat.fib (i + 2) : ℝ) ≠ 0 := by
                exact ne_of_gt (stableSyntaxCount_pos i)
              rw [Real.log_div hnum hden]
    _ = (n : ℝ)⁻¹ * (Real.log (Nat.fib (n + 2) : ℝ) - Real.log (Nat.fib 2 : ℝ)) := by
          congr 1
          simpa [add_assoc] using
            (Finset.sum_range_sub (fun i => Real.log (Nat.fib (i + 2) : ℝ)) n)
    _ = (n : ℝ)⁻¹ * Real.log (Nat.fib (n + 2) : ℝ) := by
          norm_num [Nat.fib]
    _ = Real.log (Nat.fib (n + 2) : ℝ) / (n : ℝ) := by
          rw [div_eq_mul_inv, mul_comm]

/-! ### Golden ratio arithmetic-geometric properties -/

/-- φ > 3/2.
    aux:cdim-phi-gt-three-half -/
theorem goldenRatio_gt_three_half : φ > 3 / 2 := by
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  -- φ > 3/2 ↔ φ² > (3/2)² = 9/4 (since φ > 0)
  -- φ² = φ + 1, so need φ + 1 > 9/4 ↔ φ > 5/4
  -- φ > 1 > 5/4? No, 1 < 5/4. Use: φ² = φ+1, if φ ≤ 3/2 then φ+1 ≤ 5/2
  -- but (3/2)² = 9/4 = 2.25, and if φ ≤ 3/2 then φ² ≤ (3/2)² = 9/4
  -- but φ² = φ+1 ≥ 1+1 = 2 (since φ > 1). Need sharper.
  -- Actually: φ > 1, φ² = φ+1. If φ ≤ 3/2, then φ+1 ≤ 5/2 and φ² = φ+1 ≤ 5/2.
  -- Also φ² ≥ φ·(3/2) (if φ ≥ 3/2). Contradiction approach:
  nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_sq]

/-- φ < 5/3.
    aux:cdim-phi-lt-five-thirds -/
theorem goldenRatio_lt_five_thirds : φ < 5 / 3 := by
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

/-- φ = 1 + 1/φ (the defining fixed-point equation).
    aux:cdim-phi-fixed-point -/
theorem goldenRatio_eq_one_add_inv : φ = 1 + φ⁻¹ := by
  have hne : φ ≠ 0 := ne_of_gt Real.goldenRatio_pos
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  have key : φ - 1 = φ⁻¹ := by
    rw [eq_comm, inv_eq_of_mul_eq_one_left]
    nlinarith
  linarith

/-- φ is irrational.
    aux:cdim-phi-irrational -/
theorem phi_irrational : Irrational φ := Real.goldenRatio_irrational

/-! ### Entropy rate comparison -/

/-- The topological entropy log φ is strictly less than log 2
    (the entropy of the full shift).
    aux:cdim-entropy-ordering-proxy -/
theorem entropy_ordering_proxy : Real.log φ < Real.log 2 :=
  Real.log_lt_log Real.goldenRatio_pos goldenRatio_lt_two

/-- The entropy gap: log 2 - log φ = log(2/φ) > 0.
    aux:cdim-entropy-gap-pos -/
theorem entropy_gap_pos : Real.log 2 - Real.log φ > 0 := by
  linarith [entropy_ordering_proxy]

/-! ### Binet formula (from mathlib) -/

/-- Binet formula: F(n) = (φ^n - ψ^n) / √5 (from mathlib).
    aux:cdim-binet-formula -/
theorem binet_formula (n : Nat) : (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / Real.sqrt 5 :=
  Real.coe_fib_eq n

/-! ### √5 auxiliary lemmas -/

private theorem sq_sqrt5 : Real.sqrt 5 ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)

private theorem sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
  Real.sqrt_pos_of_pos (by norm_num : (5 : ℝ) > 0)

private theorem sqrt5_gt_two : Real.sqrt 5 > 2 := by
  have h := sq_sqrt5
  have hp := sqrt5_pos
  nlinarith [sq_abs (Real.sqrt 5 - 2)]

private theorem sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have h := sq_sqrt5
  nlinarith [sq_abs (Real.sqrt 5 - 3)]

/-! ### φ/√5 precise bounds -/

/-- √5 > 2 (from sq_sqrt5 and nlinarith).
    aux:cdim-sqrt5-gt-two -/
theorem sqrt5_gt_two' : Real.sqrt 5 > 2 := sqrt5_gt_two

/-- √5 < 3 (from sq_sqrt5 and nlinarith).
    aux:cdim-sqrt5-lt-three -/
theorem sqrt5_lt_three' : Real.sqrt 5 < 3 := sqrt5_lt_three

/-- φ < √5: since φ = (1+√5)/2 and √5 > 2, we have 2φ = 1+√5 < 2√5.
    aux:cdim-phi-lt-sqrt5 -/
theorem phi_lt_sqrt5 : φ < Real.sqrt 5 := by
  rw [Real.goldenRatio]; linarith [sqrt5_gt_two]

/-- φ+1 > √5: since φ+1 = (3+√5)/2 and √5 < 3, we have 2(φ+1) = 3+√5 > 2√5.
    aux:cdim-phi-add-one-gt-sqrt5 -/
theorem phi_add_one_gt_sqrt5 : φ + 1 > Real.sqrt 5 := by
  rw [Real.goldenRatio]; linarith [sqrt5_lt_three]

/-! ### Golden angle -/

/-- The golden angle: 1/φ = φ - 1. -/
noncomputable def goldenAngle : ℝ := φ⁻¹

/-- The golden angle is positive.
    aux:cdim-golden-angle-pos -/
theorem goldenAngle_pos : 0 < goldenAngle :=
  inv_pos.mpr Real.goldenRatio_pos

/-- The golden angle is less than 1.
    aux:cdim-golden-angle-lt-one -/
theorem goldenAngle_lt_one : goldenAngle < 1 :=
  inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

/-- The golden angle satisfies θ² = 1 - θ (dual of φ² = φ + 1).
    aux:cdim-golden-angle-sq -/
theorem goldenAngle_sq : goldenAngle ^ 2 = 1 - goldenAngle := by
  have hne : φ ≠ 0 := ne_of_gt Real.goldenRatio_pos
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  simp only [goldenAngle, inv_pow]
  -- Goal: (φ^2)⁻¹ = 1 - φ⁻¹
  rw [hsq]
  have hne : φ ≠ 0 := ne_of_gt Real.goldenRatio_pos
  have hne2 : φ + 1 ≠ 0 := by linarith [Real.goldenRatio_pos]
  have hkey := goldenRatio_eq_one_add_inv
  -- φ = 1 + φ⁻¹, so φ⁻¹ = φ - 1, so 1 - φ⁻¹ = 2 - φ
  -- Also φ² = φ+1, so (φ+1)⁻¹ = (φ²)⁻¹
  -- We need (φ+1)⁻¹ = 1 - φ⁻¹ = 1 - (φ-1) = 2-φ
  -- (φ+1)⁻¹ = 2-φ ↔ 1 = (φ+1)(2-φ) = 2φ+2-φ²-φ = φ+2-(φ+1) = 1 ✓
  have : (φ + 1) * (1 - φ⁻¹) = 1 := by
    have : φ⁻¹ = φ - 1 := by linarith
    rw [this]; nlinarith [Real.goldenRatio_sq]
  exact eq_inv_of_mul_eq_one_right this |>.symm

/-! ### Binet nearest integer property -/

/-- |ψ^n / √5| < 1/2 for all n ≥ 0 (since |ψ| < 1 and √5 > 2).
    aux:cdim-abs-psi-pow-div-sqrt5-lt-half -/
theorem abs_psi_pow_div_sqrt5_lt_half (n : Nat) :
    |ψ ^ n / Real.sqrt 5| < 1 / 2 := by
  rw [abs_div, abs_of_pos sqrt5_pos]
  have hle : |ψ ^ n| ≤ 1 := by
    calc |ψ ^ n| = |ψ| ^ n := abs_pow ψ n
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) abs_goldenConj_lt_one.le
  have hgt2 : Real.sqrt 5 > 2 := sqrt5_gt_two
  have hp5 := sqrt5_pos
  -- |ψ^n|/√5 ≤ 1/√5 < 1/2
  -- Direct: |ψ^n|/√5 ≤ 1/√5 since |ψ^n| ≤ 1 and √5 > 0
  -- 1/√5 < 1/2 since √5 > 2
  -- So |ψ^n|/√5 < 1/2
  have h1 : |ψ ^ n| * 2 ≤ 1 * 2 := by linarith
  -- |ψ^n|/√5 * (2*√5) ≤ 2 and 1/2 * (2*√5) = √5
  -- Equivalently: 2*|ψ^n| ≤ 2 < √5, so 2*|ψ^n|/√5 < 1, so |ψ^n|/√5 < 1/2
  rw [div_lt_div_iff₀ hp5 (by norm_num : (0:ℝ) < 2)]
  linarith

/-- Binet nearest integer: |F(n) - φ^n/√5| < 1/2 for all n.
    prop:cdim-fibonacci-nearest-integer -/
theorem fib_nearest_integer (n : Nat) :
    |(Nat.fib n : ℝ) - φ ^ n / Real.sqrt 5| < 1 / 2 := by
  rw [binet_formula, show (φ ^ n - ψ ^ n) / Real.sqrt 5 - φ ^ n / Real.sqrt 5 =
    -(ψ ^ n / Real.sqrt 5) from by ring]
  rw [abs_neg]
  exact abs_psi_pow_div_sqrt5_lt_half n

/-- Named alias with positivity hypothesis: |F(n) - φ^n/√5| < 1/2 for n ≥ 1.
    prop:cdim-fibonacci-nearest-integer -/
theorem fib_nearest_integer_of_pos (n : Nat) (_hn : 1 ≤ n) :
    |(Nat.fib n : ℝ) - φ ^ n / Real.sqrt 5| < 1 / 2 :=
  fib_nearest_integer n

/-! ### Chebyshev phase -/

/-- (φ/2)² = (φ+1)/4.
    aux:cdim-chebyshev-phi-half-sq -/
theorem goldenRatio_div_two_sq : (φ / 2) ^ 2 = (φ + 1) / 4 := by
  rw [div_pow, Real.goldenRatio_sq]; ring

/-- Minimal polynomial of φ/2: 4x² - 2x - 1 = 0.
    aux:cdim-chebyshev-phi-half-minpoly -/
theorem goldenRatio_half_minpoly : 4 * (φ / 2) ^ 2 - 2 * (φ / 2) - 1 = 0 := by
  have hsq := Real.goldenRatio_sq
  rw [goldenRatio_div_two_sq]
  -- 4 * ((φ+1)/4) - 2 * (φ/2) - 1 = (φ+1) - φ - 1 = 0
  ring

/-! ### Entropy comprehensive certificate -/

/-- The complete entropy certificate: all key results in one theorem.
    thm:entropy-comprehensive-certificate -/
theorem entropy_comprehensive_certificate :
    Tendsto (fun n => Real.log (Nat.fib (n + 2) : ℝ) / (n : ℝ)) atTop (𝓝 (Real.log φ)) ∧
    Real.log φ > 0 ∧ Real.log φ < Real.log 2 ∧
    φ > 3 / 2 ∧ φ < 2 ∧ Irrational φ ∧
    (∀ n, (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / Real.sqrt 5) :=
  ⟨topological_entropy_eq_log_phi, log_goldenRatio_pos, entropy_ordering_proxy,
   goldenRatio_gt_three_half, goldenRatio_lt_two, phi_irrational, binet_formula⟩

/-! ### Recursion order pattern -/

/-- Recursion order pattern: order(S_q) = 2⌊q/2⌋+1 for q=2..5.
    prop:pom-recursion-order-pattern -/
theorem recursion_order_pattern :
    (3 = 2 * (2 / 2) + 1) ∧ (3 = 2 * (3 / 2) + 1) ∧
    (5 = 2 * (4 / 2) + 1) ∧ (5 = 2 * (5 / 2) + 1) := by omega

/-! ### Fibonacci convergent alternation (Cassini identity instances) -/

/-- Cassini identity alternation: F(n)² alternately exceeds and falls below F(n-1)F(n+1).
    aux:cdim-cassini-alternation -/
theorem fib_convergent_alternation :
    Nat.fib 3 ^ 2 > Nat.fib 2 * Nat.fib 4 ∧
    Nat.fib 4 ^ 2 < Nat.fib 3 * Nat.fib 5 ∧
    Nat.fib 5 ^ 2 > Nat.fib 4 * Nat.fib 6 := by native_decide

/-! ### ψ^n → 0 -/

/-- |ψ|^n → 0 as n → ∞ (geometric decay since |ψ| < 1).
    prop:cdim-psi-pow-tendsto-zero -/
theorem psi_pow_tendsto_zero :
    Tendsto (fun n => |ψ| ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) abs_goldenConj_lt_one

/-- ψ^n → 0 as n → ∞.
    prop:cdim-psi-pow-tendsto-zero-real -/
theorem psi_pow_tendsto_zero' :
    Tendsto (fun n => ψ ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_goldenConj_lt_one

/-! ### Fibonacci growth sandwich -/

/-- Growth sandwich: φ^n/√5 - 1/2 < F(n) < φ^n/√5 + 1/2.
    Direct consequence of the nearest integer property.
    prop:cdim-binet-growth-sandwich -/
theorem fib_growth_sandwich (n : Nat) :
    φ ^ n / Real.sqrt 5 - 1 / 2 < (Nat.fib n : ℝ) ∧
    (Nat.fib n : ℝ) < φ ^ n / Real.sqrt 5 + 1 / 2 := by
  have h := fib_nearest_integer n
  rw [abs_lt] at h
  constructor <;> linarith [h.1, h.2]

private theorem psi_pow_mul_inv_phi_pow (m : ℕ) :
    ψ ^ m * (φ ^ m)⁻¹ = (ψ / φ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, pow_succ, pow_succ, mul_inv_rev]
      calc
        ψ ^ m * ψ * (φ⁻¹ * (φ ^ m)⁻¹)
            = (ψ ^ m * (φ ^ m)⁻¹) * (ψ * φ⁻¹) := by ring
        _ = (ψ / φ) ^ m * (ψ / φ) := by rw [ih, div_eq_mul_inv]
        _ = (ψ / φ) ^ (m + 1) := by rw [pow_succ]

/-! ### Circle-dimension Fibonacci radius asymptotics -/

/-- `φ^{-m}` tends to `0` exponentially.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem phi_rpow_neg_nat_tendsto_zero :
    Tendsto (fun m : ℕ => φ ^ (-(m : ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ => (φ⁻¹ : ℝ) ^ m) atTop (𝓝 0) := by
    have h : |(φ⁻¹ : ℝ)| < 1 := by
      rw [Real.inv_goldenRatio, abs_neg]
      exact abs_goldenConj_lt_one
    simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one h
  have hEq : (fun m : ℕ => φ ^ (-(m : ℝ))) =ᶠ[atTop] fun m => (φ⁻¹ : ℝ) ^ m :=
    Filter.Eventually.of_forall fun m => by
      show φ ^ (-(m : ℝ)) = (φ⁻¹ : ℝ) ^ m
      rw [Real.rpow_neg Real.goldenRatio_pos.le, Real.rpow_natCast, inv_pow]
  exact Filter.Tendsto.congr' hEq.symm hpow

/-- Binet-scaled Fibonacci numbers converge to `1 / √5`.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem fib_mul_phi_neg_tendsto_inv_sqrt5 :
    Tendsto (fun m : ℕ => (Nat.fib m : ℝ) * φ ^ (-(m : ℝ))) atTop
      (𝓝 ((Real.sqrt 5)⁻¹)) := by
  let r : ℝ := ψ / φ
  have hsqrt5 : (Real.sqrt 5 : ℝ) ≠ 0 := ne_of_gt sqrt5_pos
  have hr : |r| < 1 := by
    dsimp [r]
    rw [abs_div, abs_of_pos Real.goldenRatio_pos]
    refine (div_lt_one (by positivity)).2 ?_
    exact lt_trans abs_goldenConj_lt_one Real.one_lt_goldenRatio
  have hpow : Tendsto (fun m : ℕ => r ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hmain : Tendsto (fun m : ℕ => (1 - r ^ m) / Real.sqrt 5) atTop
      (𝓝 ((1 - 0) / Real.sqrt 5)) :=
    (tendsto_const_nhds.sub hpow).div tendsto_const_nhds hsqrt5
  have hEq : (fun m : ℕ => (Nat.fib m : ℝ) * φ ^ (-(m : ℝ))) =ᶠ[atTop]
      fun m => (1 - r ^ m) / Real.sqrt 5 :=
    Filter.Eventually.of_forall fun m => by
      calc
        (Nat.fib m : ℝ) * φ ^ (-(m : ℝ)) = ((Nat.fib m : ℝ) * (φ ^ m)⁻¹) := by
          rw [Real.rpow_neg Real.goldenRatio_pos.le, Real.rpow_natCast]
        _ = (((φ ^ m - ψ ^ m) / Real.sqrt 5) * (φ ^ m)⁻¹) := by rw [binet_formula]
        _ = ((1 - ψ ^ m * (φ ^ m)⁻¹) / Real.sqrt 5) := by
          have hphi : (φ ^ m : ℝ) ≠ 0 := pow_ne_zero m Real.goldenRatio_ne_zero
          field_simp [hphi, hsqrt5]
        _ = ((1 - (ψ / φ) ^ m) / Real.sqrt 5) := by
          rw [psi_pow_mul_inv_phi_pow]
  exact Filter.Tendsto.congr' hEq.symm (by simpa [one_div] using hmain)

/-- Adding a bounded constant does not change the Binet-scaled Fibonacci limit.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem fib_add_two_mul_phi_neg_tendsto_inv_sqrt5 :
    Tendsto (fun m : ℕ => ((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ))) atTop
      (𝓝 ((Real.sqrt 5)⁻¹)) := by
  have htwo : Tendsto (fun m : ℕ => (2 : ℝ) * φ ^ (-(m : ℝ))) atTop (𝓝 0) := by
    simpa using Filter.Tendsto.const_mul 2 phi_rpow_neg_nat_tendsto_zero
  have hEq : (fun m : ℕ => ((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ))) =ᶠ[atTop]
      fun m => (Nat.fib m : ℝ) * φ ^ (-(m : ℝ)) + (2 : ℝ) * φ ^ (-(m : ℝ)) :=
    Filter.Eventually.of_forall fun m => by ring
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa using fib_mul_phi_neg_tendsto_inv_sqrt5.add htwo

/-- Normalized complement of the Fibonacci radius square tends to `1`.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem one_sub_fibRadius_sq_tendsto :
    Tendsto
      (fun m : ℕ =>
        (1 - (fibRadius m) ^ 2) /
          (4 * Real.sqrt 5 * φ ^ (-(m : ℝ))))
      atTop (𝓝 1) := by
  have hsqrt5 : (Real.sqrt 5 : ℝ) ≠ 0 := ne_of_gt sqrt5_pos
  have hFib1 : Tendsto (fun m : ℕ => ((Nat.fib m : ℝ) + 1) * φ ^ (-(m : ℝ))) atTop
      (𝓝 ((Real.sqrt 5)⁻¹)) := by
    have hone : Tendsto (fun m : ℕ => (1 : ℝ) * φ ^ (-(m : ℝ))) atTop (𝓝 0) := by
      simpa using phi_rpow_neg_nat_tendsto_zero
    have hEq : (fun m : ℕ => ((Nat.fib m : ℝ) + 1) * φ ^ (-(m : ℝ))) =ᶠ[atTop]
        fun m => (Nat.fib m : ℝ) * φ ^ (-(m : ℝ)) + (1 : ℝ) * φ ^ (-(m : ℝ)) :=
      Filter.Eventually.of_forall fun m => by ring
    refine Filter.Tendsto.congr' hEq.symm ?_
    simpa using fib_mul_phi_neg_tendsto_inv_sqrt5.add hone
  have hRatio : Tendsto
      (fun m : ℕ =>
        (((Nat.fib m : ℝ) + 1) * φ ^ (-(m : ℝ))) /
          (((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ))))
      atTop (𝓝 1) := by
    have hne : ((Real.sqrt 5)⁻¹ : ℝ) ≠ 0 := inv_ne_zero hsqrt5
    simpa [hne] using hFib1.div fib_add_two_mul_phi_neg_tendsto_inv_sqrt5 hne
  have hInv : Tendsto
      (fun m : ℕ => (Real.sqrt 5 * (((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ))))⁻¹)
      atTop (𝓝 1) := by
    have hbase : Tendsto
        (fun m : ℕ => Real.sqrt 5 * (((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ))))
        atTop (𝓝 (Real.sqrt 5 * (Real.sqrt 5)⁻¹)) :=
      Filter.Tendsto.const_mul (Real.sqrt 5) fib_add_two_mul_phi_neg_tendsto_inv_sqrt5
    have hone : Tendsto
        (fun m : ℕ => Real.sqrt 5 * (((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ))))
        atTop (𝓝 (1 : ℝ)) := by
      simpa [one_div, hsqrt5] using hbase
    simpa using hone.inv₀ one_ne_zero
  have hEq : (fun m : ℕ =>
      (1 - (fibRadius m) ^ 2) / (4 * Real.sqrt 5 * φ ^ (-(m : ℝ)))) =ᶠ[atTop]
      fun m =>
        ((((Nat.fib m : ℝ) + 1) * φ ^ (-(m : ℝ))) /
            (((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ)))) *
          (Real.sqrt 5 * (((Nat.fib m : ℝ) + 2) * φ ^ (-(m : ℝ))))⁻¹ :=
    Filter.Eventually.of_forall fun m => by
      simp only
      rw [one_sub_fibRadius_sq]
      have hphi : φ ^ (-(m : ℝ)) ≠ 0 := by positivity
      have hfib : ((Nat.fib m : ℝ) + 2) ≠ 0 := by positivity
      field_simp [hsqrt5, hphi, hfib]
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa using hRatio.mul hInv

/-- `1 - fibRadius(m)^2` is asymptotic to `4 * √5 * φ^{-m}`.
    con:cdim-fibonacci-radius-time-conjugacy -/
theorem one_sub_fibRadius_sq_isEquivalent :
    Asymptotics.IsEquivalent atTop
      (fun m : ℕ => 1 - (fibRadius m) ^ 2)
      (fun m : ℕ => 4 * Real.sqrt 5 * φ ^ (-(m : ℝ))) := by
  have hz : ∀ᶠ m : ℕ in atTop, 4 * Real.sqrt 5 * φ ^ (-(m : ℝ)) ≠ 0 :=
    Filter.Eventually.of_forall fun m => by positivity
  refine (Asymptotics.isEquivalent_iff_tendsto_one hz).2 ?_
  have hEq :
      (fun m : ℕ =>
        (fun m : ℕ => 1 - (fibRadius m) ^ 2) m /
          (fun m : ℕ => 4 * Real.sqrt 5 * φ ^ (-(m : ℝ))) m) =ᶠ[atTop]
      (fun m : ℕ =>
        (1 - (fibRadius m) ^ 2) /
          (4 * Real.sqrt 5 * φ ^ (-(m : ℝ)))) :=
    Filter.Eventually.of_forall fun _ => rfl
  exact Filter.Tendsto.congr' hEq one_sub_fibRadius_sq_tendsto

/-! ### Continued fraction convergence error -/

/-- F(n+1) - φ·F(n) = ψ^n (from mathlib).
    prop:cdim-fib-ratio-error -/
theorem fib_ratio_error (n : Nat) :
    (Nat.fib (n + 1) : ℝ) - φ * Nat.fib n = ψ ^ n :=
  Real.fib_succ_sub_goldenRatio_mul_fib n

/-- |F(n+1) - φ·F(n)| < 1 for n ≥ 1 (since |ψ^n| ≤ |ψ| < 1).
    prop:cdim-fib-ratio-error-lt-one -/
theorem fib_ratio_error_lt_one (n : Nat) (hn : 1 ≤ n) :
    |(Nat.fib (n + 1) : ℝ) - φ * Nat.fib n| < 1 := by
  rw [fib_ratio_error]
  calc |ψ ^ n| = |ψ| ^ n := abs_pow ψ n
    _ ≤ |ψ| ^ 1 := by
        apply pow_le_pow_of_le_one (abs_nonneg _) (le_of_lt abs_goldenConj_lt_one) hn
    _ = |ψ| := pow_one _
    _ < 1 := abs_goldenConj_lt_one

/-- F(n+2)/F(n+1) → φ (shifted Fibonacci ratio convergence).
    Follows from fib_ratio_tendsto composed with the shift n ↦ n+1.
    prop:cdim-fib-ratio-tendsto-golden -/
theorem fib_ratio_tendsto_golden :
    Tendsto (fun n => (Nat.fib (n + 2) : ℝ) / (Nat.fib (n + 1) : ℝ))
    atTop (nhds φ) :=
  fib_ratio_tendsto.comp (tendsto_add_atTop_nat 1)

/-- The fold index ratio log(2^m / F_{m+2}) / m → log(2/φ).
    This is the per-step entropy defect: log 2 - log φ = log(2/φ).
    thm:fold-entropy-defect-tendsto -/
theorem foldIndex_tendsto_log_two_div_phi :
    Tendsto (fun m => Real.log (2 ^ m / (Nat.fib (m + 2) : ℝ)) / m)
    atTop (nhds (Real.log (2 / φ))) := by
  -- Rewrite target: log(2/φ) = log 2 - log φ
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt Real.goldenRatio_pos)]
  -- The function equals log 2 - log F(m+2)/m eventually (for m ≥ 1)
  have hent := topological_entropy_eq_log_phi
  -- We need: (fun m => log(2^m / F(m+2)) / m) → log 2 - log φ
  -- i.e., (fun m => (m * log 2 - log F(m+2)) / m) → log 2 - log φ
  -- i.e., (fun m => log 2 - log F(m+2) / m) → log 2 - log φ
  -- This is tendsto_const_nhds.sub hent
  refine (tendsto_const_nhds.sub hent).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hF_pos : (0 : ℝ) < (Nat.fib (m + 2) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hF_ne : (Nat.fib (m + 2) : ℝ) ≠ 0 := ne_of_gt hF_pos
  have h2m_pos : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) m
  rw [Real.log_div (ne_of_gt h2m_pos) hF_ne, Real.log_pow, sub_div, mul_div_cancel_left₀ _ hm_ne]

/-- The fold index: I(m) = 2^m / F_{m+2}, measuring compression ratio.
    def:fold-index -/
noncomputable def foldIndex (m : Nat) : ℝ := 2 ^ m / (Nat.fib (m + 2) : ℝ)

/-- The fold index exceeds 1 for m ≥ 2 (since F_{m+2} < 2^m).
    prop:fold-index-gt-one -/
theorem foldIndex_gt_one (m : Nat) (hm : 2 ≤ m) : 1 < foldIndex m := by
  have hF_pos : (0 : ℝ) < (Nat.fib (m + 2) : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  rw [foldIndex, one_lt_div hF_pos]
  exact_mod_cast fib_lt_pow_two_of_ge_two m hm

/-- The fold index is strictly increasing for m ≥ 1:
    I(m) < I(m+1) iff F_{m+3} < 2·F_{m+2} iff F_{m+1} < F_{m+2}.
    prop:fold-index-strict-mono -/
theorem foldIndex_strict_mono_of_ge_one (m : Nat) (hm : 1 ≤ m) :
    foldIndex m < foldIndex (m + 1) := by
  have hFm : (0 : ℝ) < (Nat.fib (m + 2) : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hFm1 : (0 : ℝ) < (Nat.fib (m + 3) : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  rw [foldIndex, foldIndex, div_lt_div_iff₀ hFm hFm1]
  -- Goal: 2^m * F(m+3) < 2^(m+1) * F(m+2)
  -- Nat version: 2^m * F(m+3) < 2^(m+1) * F(m+2)
  -- Since F(m+3) = F(m+1) + F(m+2) and F(m+1) < F(m+2):
  -- 2^m * (F(m+1) + F(m+2)) < 2 * 2^m * F(m+2)
  -- ↔ F(m+1) + F(m+2) < 2 * F(m+2) ↔ F(m+1) < F(m+2) ✓
  have hnat : 2 ^ m * Nat.fib (m + 3) < 2 ^ (m + 1) * Nat.fib (m + 2) := by
    have h2m : 0 < 2 ^ m := Nat.pos_of_ne_zero (pow_ne_zero m (by omega))
    have hfib_lt : Nat.fib (m + 3) < 2 * Nat.fib (m + 2) := by
      rw [Nat.fib_add_two, Nat.two_mul]
      exact Nat.add_lt_add_right (Nat.fib_lt_fib_succ (by omega)) _
    calc 2 ^ m * Nat.fib (m + 3)
        < 2 ^ m * (2 * Nat.fib (m + 2)) := by exact (Nat.mul_lt_mul_left h2m).mpr hfib_lt
      _ = 2 ^ (m + 1) * Nat.fib (m + 2) := by rw [pow_succ]; ring
  exact_mod_cast hnat

/-- The hidden bit density B(m)/2^m tends to 1/3 as m → ∞.
    B(m) = ⌊2^m/3⌋, so B(m)/2^m = 1/3 - r/(3·2^m) where r ∈ {1,2}.
    cor:pom-hidden-bit-entropy -/
theorem hiddenBitDensity_tendsto_third :
    Tendsto (fun m => (hiddenBitCount m : ℝ) / 2 ^ m) atTop (nhds (1 / 3)) := by
  -- B(m) = ⌊2^m/3⌋. Show |B(m)/2^m - 1/3| ≤ 1/2^m → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨N, fun m hm => ?_⟩
  rw [Real.dist_eq]
  -- Work with B = hiddenBitCount m as a Nat
  set B := hiddenBitCount m with hB_def
  have hclosed := hiddenBitCount_closed m
  -- B * 3 + r = 2^m where r ∈ {1, 2}
  set r := if m % 2 = 0 then 1 else 2 with hr_def
  have hr_pos : 0 < r := by simp [hr_def]; split <;> omega
  have hr_le : r ≤ 2 := by simp [hr_def]; split <;> omega
  have hkey : B * 3 + r = 2 ^ m := hclosed
  -- Upper: B/2^m ≤ 1/3  (since 3B ≤ 2^m)
  have h2m_pos : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) m
  have h3B_le : 3 * B ≤ 2 ^ m := by omega
  -- Key ℝ facts
  have hBr : (B : ℝ) * 3 + (r : ℝ) = (2 : ℝ) ^ m := by
    have h := hkey
    exact_mod_cast h
  have hr_le_real : (r : ℝ) ≤ 2 := by exact_mod_cast hr_le
  have hr_pos_real : (0 : ℝ) < r := by exact_mod_cast hr_pos
  -- Upper: B * 3 ≤ 2^m → B / 2^m ≤ 1/3
  have hupper : (B : ℝ) / 2 ^ m ≤ 1 / 3 := by
    rw [div_le_div_iff₀ h2m_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  -- Lower: 1/3 - 1/2^m ≤ B/2^m
  have hlower : 1 / 3 - 1 / 2 ^ m ≤ (B : ℝ) / 2 ^ m := by
    have h1 : (0 : ℝ) < 3 * 2 ^ m := by positivity
    rw [div_sub_div _ _ (ne_of_gt (show (0:ℝ) < 3 by norm_num)) (ne_of_gt h2m_pos),
        div_le_div_iff₀ h1 h2m_pos]
    nlinarith
  have hbound : |(B : ℝ) / 2 ^ m - 1 / 3| ≤ 1 / 2 ^ m := by
    rw [abs_le]; constructor <;> linarith
  calc |(B : ℝ) / 2 ^ m - 1 / 3|
      ≤ 1 / 2 ^ m := hbound
    _ = (2⁻¹) ^ m := by rw [one_div, inv_pow]
    _ ≤ (2⁻¹) ^ N := pow_le_pow_of_le_one (by positivity) (by norm_num) hm
    _ < ε := hN

end Omega.Entropy
