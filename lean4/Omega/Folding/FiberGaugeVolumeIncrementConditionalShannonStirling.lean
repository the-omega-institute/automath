import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Folding.BinGaugeVolumeStirlingSecondOrder
import Omega.Folding.FiberGaugeVolumeChainFactorization

namespace Omega.Folding

open scoped BigOperators

/-- The leading entropy contribution in the Stirling expansion of the fiber-gauge volume
increment. -/
noncomputable def fiberGaugeConditionalShannon {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    (f : Ω → X) (π : X → Y) : ℝ := by
  classical
  exact
    ((∑ y : Y, (fiberGaugeCount (π ∘ f) y : ℝ) * Real.log (fiberGaugeCount (π ∘ f) y)) -
      ∑ x : X, (fiberGaugeCount f x : ℝ) * Real.log (fiberGaugeCount f x)) /
      (Fintype.card Ω : ℝ)

/-- The half-log correction coming from the second-order Stirling expansion. -/
noncomputable def fiberGaugeStirlingCorrection {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
    (f : Ω → X) (π : X → Y) : ℝ := by
  classical
  exact
    (1 / (2 * (Fintype.card Ω : ℝ))) *
      (((Fintype.card Y : ℝ) - Fintype.card X) * Real.log (2 * Real.pi) +
        (∑ y : Y, Real.log (fiberGaugeCount (π ∘ f) y)) -
          ∑ x : X, Real.log (fiberGaugeCount f x))

/-- Exact second-order Stirling decomposition for the fiber-gauge volume increment. -/
def fiberGaugeVolumeIncrementConditionalShannonStirling {Ω X Y : Type*} [Fintype Ω] [Fintype X]
    [Fintype Y] (f : Ω → X) (π : X → Y) : Prop := by
  classical
  exact
    ∃ ε : ℝ,
      |ε| ≤ ((Fintype.card X : ℝ) + Fintype.card Y) / (12 * Fintype.card Ω) ∧
        (Real.log (fiberGaugeCard (π ∘ f)) - Real.log (fiberGaugeCard f)) /
            (Fintype.card Ω : ℝ) =
          fiberGaugeConditionalShannon f π + fiberGaugeStirlingCorrection f π + ε

private theorem fiberGaugeCount_pos {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (u : α → β) (hsurj : Function.Surjective u) (b : β) :
    1 ≤ fiberGaugeCount u b := by
  classical
  rcases hsurj b with ⟨a, rfl⟩
  unfold fiberGaugeCount fiberGaugeFiber
  refine Nat.succ_le_of_lt ?_
  exact Finset.card_pos.mpr ⟨a, by simp⟩

private theorem log_fiberGaugeCard_eq_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (u : α → β) :
    Real.log (fiberGaugeCard u) =
      ∑ b : β, Real.log ((Nat.factorial (fiberGaugeCount u b) : ℝ)) := by
  classical
  simpa [fiberGaugeCard] using
    (Real.log_prod
      (s := (Finset.univ : Finset β))
      (f := fun b : β => ((Nat.factorial (fiberGaugeCount u b) : ℚ) : ℝ))
      (by
        intro b hb
        exact ne_of_gt (by
          exact_mod_cast Nat.factorial_pos (fiberGaugeCount u b) :
            0 < (((Nat.factorial (fiberGaugeCount u b) : ℚ) : ℝ)))))

private theorem sum_fiberGaugeCount {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (u : α → β) : ∑ b : β, fiberGaugeCount u b = Fintype.card α := by
  simpa [fiberGaugeCount, fiberGaugeFiber, Fintype.card_subtype] using
    (Fintype.sum_fiberwise (g := u) (f := fun _ : α => (1 : Nat)))

private theorem stirlingSecondOrderExpansion {α : Type*} [Fintype α] (d : α → ℕ)
    (hd : ∀ a, 1 ≤ d a) :
    ∃ R : ℝ,
      0 ≤ R ∧
        R ≤ (Fintype.card α : ℝ) / 12 ∧
          (Finset.univ.sum fun a : α => Real.log ((Nat.factorial (d a) : ℝ))) =
            (Finset.univ.sum fun a : α => (d a : ℝ) * Real.log (d a) - (d a : ℝ)) +
              (1 / 2 : ℝ) *
                  ((Fintype.card α : ℝ) * Real.log (2 * Real.pi) +
                    Finset.univ.sum (fun a : α => Real.log (d a))) +
                R := by
  let R : ℝ := ∑ a : α, stirlingSecondOrderResidual (d a)
  refine ⟨R, ?_, ?_, ?_⟩
  · unfold R
    exact Finset.sum_nonneg fun a _ => stirlingSecondOrderResidual_nonneg (hd a)
  · unfold R
    calc
      (∑ a : α, stirlingSecondOrderResidual (d a)) ≤ ∑ a : α, (1 / 12 : ℝ) := by
        exact Finset.sum_le_sum fun a _ => stirlingSecondOrderResidual_le_one_twelfth (hd a)
      _ = (Fintype.card α : ℝ) / 12 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring_nf
  · have hhalf :
        (∑ a : α, (1 / 2 : ℝ) * (Real.log (2 * Real.pi) + Real.log (d a))) =
          (1 / 2 : ℝ) *
            ((Fintype.card α : ℝ) * Real.log (2 * Real.pi) + ∑ a : α, Real.log (d a)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ]
    calc
      (∑ a : α, Real.log ((Nat.factorial (d a) : ℝ))) =
          ∑ a : α,
            ((d a : ℝ) * Real.log (d a) - (d a : ℝ) +
              (1 / 2 : ℝ) * (Real.log (2 * Real.pi) + Real.log (d a)) +
              stirlingSecondOrderResidual (d a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            unfold stirlingSecondOrderResidual
            ring
      _ = (∑ a : α, ((d a : ℝ) * Real.log (d a) - (d a : ℝ))) +
            (∑ a : α, (1 / 2 : ℝ) * (Real.log (2 * Real.pi) + Real.log (d a))) +
            ∑ a : α, stirlingSecondOrderResidual (d a) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ a : α, ((d a : ℝ) * Real.log (d a) - (d a : ℝ))) +
            (1 / 2 : ℝ) *
                ((Fintype.card α : ℝ) * Real.log (2 * Real.pi) +
                  ∑ a : α, Real.log (d a)) +
            R := by
          rw [hhalf]
      _ = (Finset.univ.sum fun a : α => (d a : ℝ) * Real.log (d a) - (d a : ℝ)) +
            (1 / 2 : ℝ) *
                ((Fintype.card α : ℝ) * Real.log (2 * Real.pi) +
                  Finset.univ.sum (fun a : α => Real.log (d a))) +
            R := by
          rfl

/-- Paper label: `prop:fiber-gauge-volume-increment-conditional-shannon-stirling`. -/
theorem paper_fiber_gauge_volume_increment_conditional_shannon_stirling {Ω X Y : Type*}
    [Fintype Ω] [Fintype X] [Fintype Y] (f : Ω → X) (π : X → Y) (hf : Function.Surjective f)
    (hπ : Function.Surjective π) : fiberGaugeVolumeIncrementConditionalShannonStirling f π := by
  classical
  by_cases hΩ0 : Fintype.card Ω = 0
  · haveI : IsEmpty Ω := Fintype.card_eq_zero_iff.mp hΩ0
    have hX0 : Fintype.card X = 0 := by
      by_contra hX0
      haveI : Nonempty X := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hX0)
      rcases hf (Classical.choice ‹Nonempty X›) with ⟨ω, _⟩
      exact isEmptyElim ω
    have hY0 : Fintype.card Y = 0 := by
      by_contra hY0
      haveI : Nonempty Y := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hY0)
      rcases hπ (Classical.choice ‹Nonempty Y›) with ⟨x, _⟩
      haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp hX0
      exact isEmptyElim x
    haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp hX0
    haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY0
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [fiberGaugeConditionalShannon, fiberGaugeStirlingCorrection]
  · have hΩpos : 0 < (Fintype.card Ω : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hΩ0
    have hΩne : (Fintype.card Ω : ℝ) ≠ 0 := hΩpos.ne'
    have hπf : Function.Surjective (π ∘ f) := hπ.comp hf
    letI : DecidableEq Ω := Classical.decEq Ω
    letI : DecidableEq X := Classical.decEq X
    letI : DecidableEq Y := Classical.decEq Y
    obtain ⟨Rf, hRf_nonneg, hRf_le, hRf_eq⟩ :=
      stirlingSecondOrderExpansion (α := X) (d := fiberGaugeCount f)
        (hd := fiberGaugeCount_pos f hf)
    obtain ⟨Rh, hRh_nonneg, hRh_le, hRh_eq⟩ :=
      stirlingSecondOrderExpansion (α := Y)
        (d := fiberGaugeCount (π ∘ f)) (hd := fiberGaugeCount_pos (π ∘ f) hπf)
    have hLogf :
        Real.log (fiberGaugeCard f) =
          (∑ x : X, ((fiberGaugeCount f x : ℝ) * Real.log (fiberGaugeCount f x) -
            (fiberGaugeCount f x : ℝ))) +
            (1 / 2 : ℝ) *
                ((Fintype.card X : ℝ) * Real.log (2 * Real.pi) +
                  ∑ x : X, Real.log (fiberGaugeCount f x)) +
              Rf := by
      simpa [log_fiberGaugeCard_eq_sum] using hRf_eq
    have hLogh :
        Real.log (fiberGaugeCard (π ∘ f)) =
          (∑ y : Y, ((fiberGaugeCount (π ∘ f) y : ℝ) * Real.log (fiberGaugeCount (π ∘ f) y) -
            (fiberGaugeCount (π ∘ f) y : ℝ))) +
            (1 / 2 : ℝ) *
                ((Fintype.card Y : ℝ) * Real.log (2 * Real.pi) +
                  ∑ y : Y, Real.log (fiberGaugeCount (π ∘ f) y)) +
              Rh := by
      simpa [log_fiberGaugeCard_eq_sum] using hRh_eq
    refine ⟨(Rh - Rf) / (Fintype.card Ω : ℝ), ?_, ?_⟩
    · have hAbsDiff : |Rh - Rf| ≤ Rh + Rf := by
        refine abs_le.mpr ?_
        constructor <;> linarith
      rw [abs_div, abs_of_nonneg hΩpos.le]
      have hnum :
          |Rh - Rf| ≤ (Fintype.card Y : ℝ) / 12 + (Fintype.card X : ℝ) / 12 := by
        linarith
      have hdiv := div_le_div_of_nonneg_right hnum hΩpos.le
      calc
        |Rh - Rf| / (Fintype.card Ω : ℝ) ≤
            ((Fintype.card Y : ℝ) / 12 + (Fintype.card X : ℝ) / 12) / (Fintype.card Ω : ℝ) := hdiv
        _ = ((Fintype.card X : ℝ) + Fintype.card Y) / (12 * Fintype.card Ω) := by
            field_simp [hΩne]
            ring
    · rw [hLogh, hLogf]
      have hSumf : (∑ x : X, (fiberGaugeCount f x : ℝ)) = Fintype.card Ω := by
        exact_mod_cast sum_fiberGaugeCount f
      have hSumh : (∑ y : Y, (fiberGaugeCount (π ∘ f) y : ℝ)) = Fintype.card Ω := by
        exact_mod_cast sum_fiberGaugeCount (π ∘ f)
      simp [fiberGaugeConditionalShannon, fiberGaugeStirlingCorrection]
      rw [hSumh, hSumf]
      field_simp [hΩne]
      ring

end Omega.Folding
