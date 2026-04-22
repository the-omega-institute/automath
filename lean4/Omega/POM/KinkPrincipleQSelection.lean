import Mathlib.Tactic

namespace Omega.POM

/-- The forward discrete slope of a function on the natural numbers. -/
def pomDiscreteSlope (b : ℕ → ℝ) (q : ℕ) : ℝ :=
  b (q + 1) - b q

/-- The finite-window kink set: the two boundary points together with the sites where the adjacent
discrete slopes are not equal. -/
def pomKinkSet (Qmax : ℕ) (b : ℕ → ℝ) : Set ℕ :=
  {q | 2 ≤ q ∧ q ≤ Qmax ∧ (q = 2 ∨ q = Qmax ∨ pomDiscreteSlope b (q - 1) ≠ pomDiscreteSlope b q)}

/-- Affine tilt of the base profile. -/
def pomAffineTilt (b : ℕ → ℝ) (a c : ℝ) (q : ℕ) : ℝ :=
  b q + a * q + c

/-- Dual minimization form of the discrete Legendre selection problem. -/
def pomDualPenalty (b : ℕ → ℝ) (γ : ℝ) (q : ℕ) : ℝ :=
  b q - (((q : ℝ) - 1) * γ)

/-- Discrete convexity on the window `[2, Qmax]`. -/
def PomDiscreteConvexOn (Qmax : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ q : ℕ, 2 ≤ q → q + 1 ≤ Qmax → pomDiscreteSlope b (q - 1) ≤ pomDiscreteSlope b q

/-- Optimality on the finite window `[2, Qmax]`. -/
def pomOptimalInWindow (f : ℕ → ℝ) (Qmax q : ℕ) : Prop :=
  2 ≤ q ∧ q ≤ Qmax ∧ ∀ r : ℕ, 2 ≤ r → r ≤ Qmax → f q ≤ f r

/-- Publication-facing discrete kink principle: every affine tilt and its dual slope reformulation
admit an optimal point on the finite kink set. -/
def PomKinkPrincipleQSelectionStatement (Qmax : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ hQ : 2 ≤ Qmax, PomDiscreteConvexOn Qmax b →
    (∀ a c : ℝ, ∃ q : ℕ, q ∈ pomKinkSet Qmax b ∧ pomOptimalInWindow (pomAffineTilt b a c) Qmax q) ∧
    ∀ γ : ℝ, ∃ q : ℕ, q ∈ pomKinkSet Qmax b ∧ pomOptimalInWindow (pomDualPenalty b γ) Qmax q

private theorem exists_optimal_in_window (Qmax : ℕ) (hQ : 2 ≤ Qmax) (f : ℕ → ℝ) :
    ∃ q : ℕ, pomOptimalInWindow f Qmax q := by
  let s : Finset ℕ := Finset.Icc 2 Qmax
  have hs : s.Nonempty := ⟨2, by simp [s, hQ]⟩
  rcases Finset.exists_min_image s f hs with ⟨q, hq, hmin⟩
  refine ⟨q, ?_⟩
  rcases Finset.mem_Icc.mp hq with ⟨hq2, hqQ⟩
  refine ⟨hq2, hqQ, ?_⟩
  intro r hr2 hrQ
  exact hmin r (by simp [s, hr2, hrQ])

private theorem leftmost_optimal_is_kink (Qmax : ℕ) (hQ : 2 ≤ Qmax) (f : ℕ → ℝ) :
    ∃ q : ℕ, q ∈ pomKinkSet Qmax f ∧ pomOptimalInWindow f Qmax q := by
  classical
  have hex : ∃ q : ℕ, pomOptimalInWindow f Qmax q := exists_optimal_in_window Qmax hQ f
  let q : ℕ := Nat.find hex
  have hqopt : pomOptimalInWindow f Qmax q := Nat.find_spec hex
  refine ⟨q, ?_, hqopt⟩
  rcases hqopt with ⟨hq2, hqQ, hmin⟩
  by_cases hq_left : q = 2
  · exact ⟨hq2, hqQ, Or.inl hq_left⟩
  by_cases hq_right : q = Qmax
  · exact ⟨hq2, hqQ, Or.inr <| Or.inl hq_right⟩
  have hprev_not_opt : ¬ pomOptimalInWindow f Qmax (q - 1) := by
    intro hprev
    have hleast : q ≤ q - 1 := Nat.find_min' hex hprev
    omega
  have hq_le_prev : f q ≤ f (q - 1) := hmin (q - 1) (by omega) (by omega)
  have hprev_not_le : ¬ f (q - 1) ≤ f q := by
    intro hle
    have hprev_opt : pomOptimalInWindow f Qmax (q - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      intro r hr2 hrQ
      exact hle.trans (hmin r hr2 hrQ)
    exact hprev_not_opt hprev_opt
  have hprev_gt : f q < f (q - 1) := by
    have hneq : f q ≠ f (q - 1) := by
      intro heq
      exact hprev_not_le (le_of_eq heq.symm)
    exact lt_of_le_of_ne hq_le_prev hneq
  have hnext_ge : f q ≤ f (q + 1) := hmin (q + 1) (by omega) (by omega)
  have hslope_change : pomDiscreteSlope f (q - 1) ≠ pomDiscreteSlope f q := by
    have hneg : pomDiscreteSlope f (q - 1) < 0 := by
      have hpred : q - 1 + 1 = q := by omega
      rw [pomDiscreteSlope, hpred]
      exact sub_lt_zero.mpr hprev_gt
    have hnonneg : 0 ≤ pomDiscreteSlope f q := by
      simpa [pomDiscreteSlope] using sub_nonneg.mpr hnext_ge
    have hlt : pomDiscreteSlope f (q - 1) < pomDiscreteSlope f q := lt_of_lt_of_le hneg hnonneg
    exact ne_of_lt hlt
  exact ⟨hq2, hqQ, Or.inr <| Or.inr hslope_change⟩

private lemma pomDiscreteSlope_affine (b : ℕ → ℝ) (a c : ℝ) (q : ℕ) :
    pomDiscreteSlope (pomAffineTilt b a c) q = pomDiscreteSlope b q + a := by
  calc
    pomDiscreteSlope (pomAffineTilt b a c) q
      = (b (q + 1) + a * ((q + 1 : ℕ) : ℝ) + c) - (b q + a * (q : ℝ) + c) := by rfl
    _ = (b (q + 1) - b q) + a * ((((q + 1 : ℕ) : ℝ) - (q : ℝ))) := by ring
    _ = pomDiscreteSlope b q + a := by
      norm_num [pomDiscreteSlope]

private lemma pomKinkSet_affine (Qmax : ℕ) (b : ℕ → ℝ) (a c : ℝ) :
    pomKinkSet Qmax (pomAffineTilt b a c) = pomKinkSet Qmax b := by
  ext q
  simp [pomKinkSet, pomDiscreteSlope_affine, add_left_inj]

private lemma pomDualPenalty_eq_affine (b : ℕ → ℝ) (γ : ℝ) :
    pomDualPenalty b γ = pomAffineTilt b (-γ) γ := by
  funext q
  unfold pomDualPenalty pomAffineTilt
  ring

/-- Paper label: `prop:pom-kink-principle-q-selection`. -/
theorem paper_pom_kink_principle_q_selection (Qmax : ℕ) (b : ℕ → ℝ) :
    PomKinkPrincipleQSelectionStatement Qmax b := by
  intro hQ _hconv
  constructor
  · intro a c
    obtain ⟨q, hqkink, hqopt⟩ := leftmost_optimal_is_kink Qmax hQ (pomAffineTilt b a c)
    refine ⟨q, ?_, hqopt⟩
    simpa [pomKinkSet_affine] using hqkink
  · intro γ
    obtain ⟨q, hqkink, hqopt⟩ := leftmost_optimal_is_kink Qmax hQ (pomDualPenalty b γ)
    refine ⟨q, ?_, hqopt⟩
    rw [pomDualPenalty_eq_affine, pomKinkSet_affine] at hqkink
    exact hqkink

end Omega.POM
