import Mathlib.Tactic

namespace Omega.Conclusion

/-- Agreement of two Boolean semantic streams on the first `n` audit positions. -/
def conclusion_global_strictification_sideband_inapproximability_prefixAgree
    (n : ℕ) (f g : ℕ → Bool) : Prop :=
  ∀ k : ℕ, k < n → f k = g k

/-- A finite strictifier of depth `n` would make first-`n` agreement determine the whole stream. -/
def conclusion_global_strictification_sideband_inapproximability_finiteStrictifierSound
    (n : ℕ) : Prop :=
  ∀ f g : ℕ → Bool,
    conclusion_global_strictification_sideband_inapproximability_prefixAgree n f g → f = g

/-- The two-sided additive error window of radius strictly less than one, stated arithmetically. -/
def conclusion_global_strictification_sideband_inapproximability_additiveUnitApprox
    (a target : ℕ → ℕ) : Prop :=
  ∀ π : ℕ, a π < target π + 1 ∧ target π < a π + 1

/-- A concrete zero-budget sideband bit. -/
def conclusion_global_strictification_sideband_inapproximability_zeroSideband
    (π : ℕ) : ℕ :=
  if π = 0 then 0 else 1

/-- A gap-amplified sideband budget used to record the factor-two separation threshold. -/
def conclusion_global_strictification_sideband_inapproximability_gapSideband
    (π : ℕ) : ℕ :=
  if π = 0 then 1 else 3

/-- A one-sided multiplicative estimate with factor strictly below two. -/
def conclusion_global_strictification_sideband_inapproximability_subTwoMultiplicativeApprox
    (a target : ℕ → ℕ) : Prop :=
  ∀ π : ℕ, target π ≤ a π ∧ a π < 2 * target π

/-- Concrete finite-prefix and sideband approximation package for the conclusion theorem. -/
def conclusion_global_strictification_sideband_inapproximability_statement : Prop :=
  (∀ n : ℕ,
    ¬ conclusion_global_strictification_sideband_inapproximability_finiteStrictifierSound n) ∧
  (∀ n : ℕ, ∃ f g : ℕ → Bool,
    conclusion_global_strictification_sideband_inapproximability_prefixAgree n f g ∧ f ≠ g) ∧
  (∀ a : ℕ → ℕ,
    conclusion_global_strictification_sideband_inapproximability_additiveUnitApprox a
        conclusion_global_strictification_sideband_inapproximability_zeroSideband →
      ∀ π : ℕ, (a π = 0 ↔ π = 0)) ∧
  (∀ a : ℕ → ℕ,
    conclusion_global_strictification_sideband_inapproximability_subTwoMultiplicativeApprox a
        conclusion_global_strictification_sideband_inapproximability_gapSideband →
      a 0 = 1 ∧ 3 ≤ a 1)

theorem paper_conclusion_global_strictification_sideband_inapproximability :
    conclusion_global_strictification_sideband_inapproximability_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hsound
    let f : ℕ → Bool := fun _ => false
    let g : ℕ → Bool := fun k => decide (k = n)
    have hagree :
        conclusion_global_strictification_sideband_inapproximability_prefixAgree n f g := by
      intro k hk
      dsimp [f, g]
      have hkn : k ≠ n := by omega
      simp [hkn]
    have hfg : f = g := hsound f g hagree
    have hfalse : false = true := by
      calc
        false = f n := rfl
        _ = g n := congrFun hfg n
        _ = true := by simp [g]
    cases hfalse
  · intro n
    let f : ℕ → Bool := fun _ => false
    let g : ℕ → Bool := fun k => decide (k = n)
    refine ⟨f, g, ?_, ?_⟩
    · intro k hk
      dsimp [f, g]
      have hkn : k ≠ n := by omega
      simp [hkn]
    · intro hfg
      have hfalse : false = true := by
        calc
          false = f n := rfl
          _ = g n := congrFun hfg n
          _ = true := by simp [g]
      cases hfalse
  · intro a ha π
    constructor
    · intro hzero
      by_contra hπ
      specialize ha π
      simp [conclusion_global_strictification_sideband_inapproximability_zeroSideband, hπ] at ha
      omega
    · intro hπ
      subst π
      specialize ha 0
      simp [conclusion_global_strictification_sideband_inapproximability_zeroSideband] at ha
      omega
  · intro a ha
    constructor
    · specialize ha 0
      simp [conclusion_global_strictification_sideband_inapproximability_gapSideband] at ha
      omega
    · specialize ha 1
      simp [conclusion_global_strictification_sideband_inapproximability_gapSideband] at ha
      omega

end Omega.Conclusion
