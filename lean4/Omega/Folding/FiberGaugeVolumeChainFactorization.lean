import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

/-- Concrete finite chain data `α --f--> β --g--> γ` used for the fiber-gauge factorization. -/
structure FiberGaugeVolumeChainData where
  α : Type*
  β : Type*
  γ : Type*
  instFintypeα : Fintype α
  instDecidableEqα : DecidableEq α
  instFintypeβ : Fintype β
  instDecidableEqβ : DecidableEq β
  instFintypeγ : Fintype γ
  instDecidableEqγ : DecidableEq γ
  f : α → β
  g : β → γ

attribute [instance] FiberGaugeVolumeChainData.instFintypeα
attribute [instance] FiberGaugeVolumeChainData.instDecidableEqα
attribute [instance] FiberGaugeVolumeChainData.instFintypeβ
attribute [instance] FiberGaugeVolumeChainData.instDecidableEqβ
attribute [instance] FiberGaugeVolumeChainData.instFintypeγ
attribute [instance] FiberGaugeVolumeChainData.instDecidableEqγ

/-- The composed map `h = g ∘ f`. -/
def FiberGaugeVolumeChainData.h (D : FiberGaugeVolumeChainData) : D.α → D.γ :=
  D.g ∘ D.f

/-- The finite fiber of `u` over `y`. -/
def fiberGaugeFiber {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (u : α → β)
    (y : β) : Finset α :=
  Finset.univ.filter fun a => u a = y

/-- Cardinality of the fiber of `u` over `y`. -/
def fiberGaugeCount {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (u : α → β)
    (y : β) : Nat :=
  (fiberGaugeFiber u y).card

/-- The gauge volume of a finite map: product of factorial fiber sizes. -/
def fiberGaugeCard {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (u : α → β) : ℚ :=
  ∏ y : β, (Nat.factorial (fiberGaugeCount u y) : ℚ)

/-- The chain merge factor is the explicit quotient between the composed gauge volume and the
intermediate gauge volume. -/
def fiberGaugeMergeFactor (D : FiberGaugeVolumeChainData) : ℚ :=
  fiberGaugeCard D.h / fiberGaugeCard D.f

private theorem fiberGaugeCard_ne_zero {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (u : α → β) : fiberGaugeCard u ≠ 0 := by
  classical
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro y hy
  exact_mod_cast Nat.factorial_ne_zero (fiberGaugeCount u y)

private theorem log_factorial_le_mul_log (n : ℕ) :
    Real.log ((Nat.factorial n : ℝ)) ≤ (n : ℝ) * Real.log n := by
  have hfac_pos : 0 < ((Nat.factorial n : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hfac_le : ((Nat.factorial n : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  calc
    Real.log ((Nat.factorial n : ℝ)) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hfac_pos hfac_le
    _ = (n : ℝ) * Real.log n := by rw [Real.log_pow]

private theorem mul_log_sub_self_add_one_le_log_factorial {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - (n : ℝ) + 1 ≤ Real.log ((Nat.factorial n : ℝ)) := by
  by_cases h1 : n = 1
  · subst h1
    norm_num [Nat.factorial]
  · have hn2 : 2 ≤ n := by omega
    have hstirling :=
      Stirling.le_log_factorial_stirling (n := n) (by omega : n ≠ 0)
    have hlog_part : (1 : ℝ) ≤ Real.log (n : ℝ) / 2 + Real.log (2 * Real.pi) / 2 := by
      have hExpTwo : Real.exp 2 ≤ (n : ℝ) * (2 * Real.pi) := by
        have hExpTwoLtNine : Real.exp 2 < 9 := by
          calc
            Real.exp 2 = Real.exp 1 * Real.exp 1 := by
              rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
            _ < 3 * 3 := by
              gcongr <;> exact Real.exp_one_lt_three
            _ = 9 := by norm_num
        have hNineLtFourPi : (9 : ℝ) < 4 * Real.pi := by
          nlinarith [Real.pi_gt_three]
        have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        calc
          Real.exp 2 ≤ 9 := hExpTwoLtNine.le
          _ ≤ 4 * Real.pi := hNineLtFourPi.le
          _ ≤ (n : ℝ) * (2 * Real.pi) := by
            nlinarith [hnR, Real.pi_pos]
      have hlog_mul : Real.log ((n : ℝ) * (2 * Real.pi)) = Real.log n + Real.log (2 * Real.pi) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      have hlog_ge_two : (2 : ℝ) ≤ Real.log ((n : ℝ) * (2 * Real.pi)) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        simpa using hExpTwo
      rw [hlog_mul] at hlog_ge_two
      linarith
    linarith

/-- Fiber-gauge chain factorization: the composed gauge volume factors as the product of the
source gauge volume and the multinomial merge quotient over the target fibers.
    thm:fiber-gauge-volume-chain-factorization -/
theorem paper_fiber_gauge_volume_chain_factorization (D : FiberGaugeVolumeChainData) :
    fiberGaugeCard D.h = fiberGaugeCard D.f * fiberGaugeMergeFactor D := by
  have hf_ne : fiberGaugeCard D.f ≠ 0 := fiberGaugeCard_ne_zero D.f
  unfold fiberGaugeMergeFactor
  field_simp [hf_ne]

/-- The logarithmic density of the fiber-gauge volume sits between the averaged conditional
entropy term `H` and its first-order Stirling correction. -/
theorem paper_fiber_gauge_volume_density_vs_conditional_entropy {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (u : α → β) (hsurj : Function.Surjective u) :
    let A : ℝ := Fintype.card α
    let B : ℝ := Fintype.card β
    let H := (∑ b : β, (fiberGaugeCount u b : ℝ) * Real.log (fiberGaugeCount u b)) / A
    let g := Real.log (fiberGaugeCard u) / A
    H - 1 + B / A ≤ g ∧ g ≤ H := by
  classical
  by_cases hα0 : Fintype.card α = 0
  · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hα0
    have hβ0 : Fintype.card β = 0 := by
      by_contra hβ0
      have hβpos : 0 < Fintype.card β := Nat.pos_of_ne_zero hβ0
      haveI : Nonempty β := Fintype.card_pos_iff.mp hβpos
      rcases hsurj (Classical.choice ‹Nonempty β›) with ⟨a, _⟩
      exact isEmptyElim a
    haveI : IsEmpty β := Fintype.card_eq_zero_iff.mp hβ0
    simp [fiberGaugeCard]
  · have hApos_nat : 0 < Fintype.card α := Nat.pos_of_ne_zero hα0
    have hApos : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hApos_nat
    have hAne : (Fintype.card α : ℝ) ≠ 0 := hApos.ne'
    have hcount_pos : ∀ b : β, 0 < fiberGaugeCount u b := by
      intro b
      rcases hsurj b with ⟨a, rfl⟩
      unfold fiberGaugeCount fiberGaugeFiber
      refine Finset.card_pos.mpr ?_
      exact ⟨a, by simp⟩
    have hlogCard :
        Real.log (fiberGaugeCard u) =
          ∑ b : β, Real.log ((Nat.factorial (fiberGaugeCount u b) : ℝ)) := by
      simpa [fiberGaugeCard] using
        (Real.log_prod
          (s := (Finset.univ : Finset β))
          (f := fun y : β => ((Nat.factorial (fiberGaugeCount u y) : ℚ) : ℝ))
          (by
            intro b hb
            exact ne_of_gt (by
              exact_mod_cast Nat.factorial_pos (fiberGaugeCount u b) : 0 <
                (((Nat.factorial (fiberGaugeCount u b) : ℚ) : ℝ)))))
    have hsumCounts_nat : ∑ b : β, fiberGaugeCount u b = Fintype.card α := by
      simpa [fiberGaugeCount, fiberGaugeFiber, Fintype.card_subtype] using
        (Fintype.sum_fiberwise (g := u) (f := fun _ : α => (1 : Nat)))
    have hsumCounts :
        (∑ b : β, (fiberGaugeCount u b : ℝ)) = Fintype.card α := by
      exact_mod_cast hsumCounts_nat
    have hlower :
        (∑ b : β, (fiberGaugeCount u b : ℝ) * Real.log (fiberGaugeCount u b)) -
            Fintype.card α + Fintype.card β ≤
          Real.log (fiberGaugeCard u) := by
      calc
        (∑ b : β, (fiberGaugeCount u b : ℝ) * Real.log (fiberGaugeCount u b)) -
              Fintype.card α + Fintype.card β =
            ∑ b : β,
              ((fiberGaugeCount u b : ℝ) * Real.log (fiberGaugeCount u b) -
                (fiberGaugeCount u b : ℝ) + 1) := by
                  have hsumOnes : (∑ _ : β, (1 : ℝ)) = Fintype.card β := by simp
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumCounts, hsumOnes]
        _ ≤ ∑ b : β, Real.log ((Nat.factorial (fiberGaugeCount u b) : ℝ)) := by
              exact Finset.sum_le_sum fun b _ =>
                mul_log_sub_self_add_one_le_log_factorial (Nat.succ_le_of_lt (hcount_pos b))
        _ = Real.log (fiberGaugeCard u) := hlogCard.symm
    have hupper :
        Real.log (fiberGaugeCard u) ≤
          ∑ b : β, (fiberGaugeCount u b : ℝ) * Real.log (fiberGaugeCount u b) := by
      rw [hlogCard]
      exact Finset.sum_le_sum fun b _ => log_factorial_le_mul_log (fiberGaugeCount u b)
    let A : ℝ := Fintype.card α
    let B : ℝ := Fintype.card β
    let S : ℝ := ∑ b : β, (fiberGaugeCount u b : ℝ) * Real.log (fiberGaugeCount u b)
    let L : ℝ := Real.log (fiberGaugeCard u)
    have hApos' : 0 < A := by simpa [A]
    have hAne' : A ≠ 0 := hApos'.ne'
    have hLowerDiv : (S - A + B) / A ≤ L / A := by
      exact div_le_div_of_nonneg_right (by simpa [A, B, S, L] using hlower) hApos'.le
    have hUpperDiv : L / A ≤ S / A := by
      exact div_le_div_of_nonneg_right (by simpa [A, S, L] using hupper) hApos'.le
    have hLowerRewrite : (S - A + B) / A = S / A - 1 + B / A := by
      field_simp [hAne']
    refine ⟨?_, ?_⟩
    · rw [← hLowerRewrite]
      simpa [A, B, S, L] using hLowerDiv
    · simpa [A, S, L] using hUpperDiv

end Omega.Folding
