import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
import Omega.Folding.FiberGaugeVolumeChainFactorization

namespace Omega.Folding

open scoped BigOperators

/-- The multinomial correction contributed by the `γ`-fiber over `z`. -/
def fiberGaugeConditionalLocalCoeff (D : FiberGaugeVolumeChainData) (z : D.γ) : ℕ :=
  Nat.multinomial (Finset.univ : Finset {y : D.β // D.g y = z})
    (fun y => fiberGaugeCount D.f y.1)

/-- The source-side density `log vol(f) / |α|`. -/
noncomputable def fiberGaugeSourceDensity (D : FiberGaugeVolumeChainData) : ℝ :=
  Real.log (fiberGaugeCard D.f) / Fintype.card D.α

/-- The target-side density `log vol(g ∘ f) / |α|`. -/
noncomputable def fiberGaugeTargetDensity (D : FiberGaugeVolumeChainData) : ℝ :=
  Real.log (fiberGaugeCard D.h) / Fintype.card D.α

/-- Exact density identity plus monotonicity and equality criterion for the conditional factorial
chain along `α --f--> β --g--> γ`. -/
def FiberGaugeConditionalFactorialChain (D : FiberGaugeVolumeChainData) : Prop :=
  fiberGaugeTargetDensity D =
      fiberGaugeSourceDensity D + Real.log (fiberGaugeMergeFactor D) / Fintype.card D.α ∧
    fiberGaugeSourceDensity D ≤ fiberGaugeTargetDensity D ∧
    (fiberGaugeTargetDensity D = fiberGaugeSourceDensity D ↔ fiberGaugeMergeFactor D = 1)

private def fiberGaugeChainFiberEquiv (D : FiberGaugeVolumeChainData) (z : D.γ) :
    {a : D.α // D.h a = z} ≃ Σ y : {y : D.β // D.g y = z}, {a : D.α // D.f a = y.1} where
  toFun a := ⟨⟨D.f a.1, a.2⟩, ⟨a.1, rfl⟩⟩
  invFun y := ⟨y.2.1, by
    change D.g (D.f y.2.1) = z
    exact (by rw [y.2.2]; exact y.1.2)⟩
  left_inv a := by
    cases a
    rfl
  right_inv y := by
    rcases y with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
    cases ha
    rfl

private lemma fiberGaugeCount_h_eq_sum (D : FiberGaugeVolumeChainData) (z : D.γ) :
    fiberGaugeCount D.h z = ∑ y : {y : D.β // D.g y = z}, fiberGaugeCount D.f y.1 := by
  calc
    fiberGaugeCount D.h z = Fintype.card {a : D.α // D.h a = z} := by
      simp [fiberGaugeCount, fiberGaugeFiber, Fintype.card_subtype]
    _ =
        Fintype.card (Σ y : {y : D.β // D.g y = z}, {a : D.α // D.f a = y.1}) := by
          exact Fintype.card_congr (fiberGaugeChainFiberEquiv D z)
    _ = ∑ y : {y : D.β // D.g y = z}, Fintype.card {a : D.α // D.f a = y.1} := by
          simp [Fintype.card_sigma]
    _ = ∑ y : {y : D.β // D.g y = z}, fiberGaugeCount D.f y.1 := by
          simp [fiberGaugeCount, fiberGaugeFiber, Fintype.card_subtype]

private lemma fiberGaugeLocalFactor (D : FiberGaugeVolumeChainData) (z : D.γ) :
    (∏ y : {y : D.β // D.g y = z}, (Nat.factorial (fiberGaugeCount D.f y.1) : ℚ)) *
        (fiberGaugeConditionalLocalCoeff D z : ℚ) =
      (Nat.factorial (fiberGaugeCount D.h z) : ℚ) := by
  exact_mod_cast
    (by
      simpa [fiberGaugeConditionalLocalCoeff, fiberGaugeCount_h_eq_sum D z] using
        (Nat.multinomial_spec (s := (Finset.univ : Finset {y : D.β // D.g y = z}))
          (f := fun y => fiberGaugeCount D.f y.1)))

private lemma fiberGaugeCard_fiberwise (D : FiberGaugeVolumeChainData) :
    fiberGaugeCard D.f =
      ∏ z : D.γ, ∏ y : {y : D.β // D.g y = z}, (Nat.factorial (fiberGaugeCount D.f y.1) : ℚ) := by
  classical
  let e : D.β → Σ z : D.γ, {y : D.β // D.g y = z} := fun y => ⟨D.g y, ⟨y, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro y₁ y₂ h
      simpa [e] using congrArg (fun yz => yz.2.1) h
    · intro yz
      refine ⟨yz.2.1, ?_⟩
      rcases yz with ⟨z, ⟨y, hy⟩⟩
      cases hy
      rfl
  calc
    fiberGaugeCard D.f = ∏ y : D.β, (Nat.factorial (fiberGaugeCount D.f y) : ℚ) := rfl
    _ = ∏ yz : Σ z : D.γ, {y : D.β // D.g y = z},
          (Nat.factorial (fiberGaugeCount D.f yz.2.1) : ℚ) := by
            exact Fintype.prod_bijective e he
              (fun y => (Nat.factorial (fiberGaugeCount D.f y) : ℚ))
              (fun yz => (Nat.factorial (fiberGaugeCount D.f yz.2.1) : ℚ))
              (by intro y; rfl)
    _ = ∏ z : D.γ, ∏ y : {y : D.β // D.g y = z},
          (Nat.factorial (fiberGaugeCount D.f y.1) : ℚ) := by
            simpa using
              (Fintype.prod_sigma (fun yz : Σ z : D.γ, {y : D.β // D.g y = z} =>
                (Nat.factorial (fiberGaugeCount D.f yz.2.1) : ℚ)))

private lemma fiberGaugeMergeFactor_product (D : FiberGaugeVolumeChainData) :
    fiberGaugeMergeFactor D = ∏ z : D.γ, (fiberGaugeConditionalLocalCoeff D z : ℚ) := by
  have hfactor :
      fiberGaugeCard D.f * ∏ z : D.γ, (fiberGaugeConditionalLocalCoeff D z : ℚ) =
        fiberGaugeCard D.h := by
    rw [fiberGaugeCard_fiberwise D, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro z hz
    simpa using fiberGaugeLocalFactor D z
  have hf_ne : fiberGaugeCard D.f ≠ 0 := by
    classical
    unfold fiberGaugeCard
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro y hy
    exact_mod_cast Nat.factorial_ne_zero (fiberGaugeCount D.f y)
  unfold fiberGaugeMergeFactor
  apply (div_eq_iff hf_ne).2
  simpa [mul_comm] using hfactor.symm

private lemma fiberGaugeMergeFactor_one_le (D : FiberGaugeVolumeChainData) :
    (1 : ℚ) ≤ fiberGaugeMergeFactor D := by
  rw [fiberGaugeMergeFactor_product D]
  rw [← Finset.prod_natCast]
  exact_mod_cast Nat.succ_le_of_lt
    (Finset.prod_pos fun z _ =>
      Nat.multinomial_pos (s := (Finset.univ : Finset {y : D.β // D.g y = z}))
        (f := fun y => fiberGaugeCount D.f y.1))

/-- Paper label: `cor:fiber-gauge-volume-density-conditional-factorial-chain`. Taking logarithms
of the chain-factorization identity yields the exact density formula; positivity of the
multinomial correction gives monotonicity, and equality is equivalent to a trivial correction. -/
theorem paper_fiber_gauge_volume_density_conditional_factorial_chain
    (D : FiberGaugeVolumeChainData) : FiberGaugeConditionalFactorialChain D := by
  by_cases hA0 : Fintype.card D.α = 0
  · have hsource : fiberGaugeSourceDensity D = 0 := by
      simp [fiberGaugeSourceDensity, hA0]
    have htarget : fiberGaugeTargetDensity D = 0 := by
      simp [fiberGaugeTargetDensity, hA0]
    have hmerge : fiberGaugeMergeFactor D = 1 := by
      haveI : IsEmpty D.α := Fintype.card_eq_zero_iff.mp hA0
      rw [fiberGaugeMergeFactor_product D]
      refine Finset.prod_eq_one ?_
      intro z hz
      have hcount_zero : ∀ y : {y : D.β // D.g y = z}, fiberGaugeCount D.f y.1 = 0 := by
        intro y
        simp [fiberGaugeCount, fiberGaugeFiber]
      simp [fiberGaugeConditionalLocalCoeff, hcount_zero, Nat.multinomial]
    refine ⟨?_, ?_, ?_⟩
    · rw [htarget, hsource, hmerge]
      simp [hA0]
    · rw [hsource, htarget]
    · rw [htarget, hsource]
      simp [hmerge]
  · have hApos_nat : 0 < Fintype.card D.α := Nat.pos_of_ne_zero hA0
    have hApos : 0 < (Fintype.card D.α : ℝ) := by exact_mod_cast hApos_nat
    have hAne : (Fintype.card D.α : ℝ) ≠ 0 := hApos.ne'
    have hmerge_one_le_real : (1 : ℝ) ≤ (fiberGaugeMergeFactor D : ℝ) := by
      exact_mod_cast fiberGaugeMergeFactor_one_le D
    have hmerge_pos : 0 < (fiberGaugeMergeFactor D : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (show (0 : ℚ) < 1 by norm_num) (fiberGaugeMergeFactor_one_le D)
    have hmerge_nonneg : 0 ≤ Real.log (fiberGaugeMergeFactor D) := by
      exact Real.log_nonneg hmerge_one_le_real
    have hfactor := paper_fiber_gauge_volume_chain_factorization D
    have hf_pos_rat : (0 : ℚ) < fiberGaugeCard D.f := by
      unfold fiberGaugeCard
      exact Finset.prod_pos fun y _ => by
        exact_mod_cast Nat.factorial_pos (fiberGaugeCount D.f y)
    have hf_pos : 0 < (fiberGaugeCard D.f : ℝ) := by
      exact_mod_cast hf_pos_rat
    have hf_ne : (fiberGaugeCard D.f : ℝ) ≠ 0 := ne_of_gt hf_pos
    have hmerge_ne : (fiberGaugeMergeFactor D : ℝ) ≠ 0 := ne_of_gt hmerge_pos
    have hdensity :
        fiberGaugeTargetDensity D =
          fiberGaugeSourceDensity D + Real.log (fiberGaugeMergeFactor D) / Fintype.card D.α := by
      unfold fiberGaugeTargetDensity fiberGaugeSourceDensity
      rw [hfactor, Rat.cast_mul, Real.log_mul hf_ne hmerge_ne]
      field_simp [hAne]
    refine ⟨hdensity, ?_, ?_⟩
    · rw [hdensity]
      have : 0 ≤ Real.log (fiberGaugeMergeFactor D) / Fintype.card D.α := by
        exact div_nonneg hmerge_nonneg hApos.le
      linarith
    · constructor
      · intro heq
        have hlog_zero : Real.log (fiberGaugeMergeFactor D) = 0 := by
          have hdiv :
              Real.log (fiberGaugeMergeFactor D) / Fintype.card D.α = 0 := by
            linarith [hdensity, heq]
          exact ((div_eq_zero_iff).mp hdiv).resolve_right hAne
        rcases Real.log_eq_zero.mp hlog_zero with hzero | hone | hnegone
        · exact (hmerge_ne hzero).elim
        · exact_mod_cast hone
        · linarith
      · intro hmerge
        rw [hdensity, hmerge]
        simp

end Omega.Folding
