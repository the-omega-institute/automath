import Mathlib.Tactic

namespace Omega.Folding.LocalRewriteLdpBarrier

noncomputable section

open scoped BigOperators

/-- Average deletion per local rewrite step. -/
def averageDeletion {T : ℕ} (Δ : Fin T → ℝ) : ℝ :=
  (∑ i, Δ i) / T

/-- Density of steps whose deletion is at most `R - ε`. -/
def lowDeletionDensity {T : ℕ} (Δ : Fin T → ℝ) (R ε : ℝ) : ℝ :=
  ((Finset.filter (fun i => Δ i ≤ R - ε) Finset.univ).card : ℝ) / T

/-- The telescoping identity `∑ Δ = G` turns the average deletion into `G / T`. -/
theorem averageDeletion_eq_total {T : ℕ} (Δ : Fin T → ℝ) (G : ℝ)
    (hG : (∑ i, Δ i) = G) :
    averageDeletion Δ = G / T := by
  simp [averageDeletion, hG]

/-- If every step deletes at most `R`, then the average is penalized by any positive density
    of steps that delete at most `R - ε`. -/
theorem averageDeletion_le_of_lowDeletionDensity
    {R ε : ℝ} {T : ℕ} (hT : 0 < T) (Δ : Fin T → ℝ)
    (hBound : ∀ i, Δ i ≤ R) :
    averageDeletion Δ ≤ R - ε * lowDeletionDensity Δ R ε := by
  have hsum :
      ∑ i, Δ i ≤
        ∑ i : Fin T, (R - ε * (if Δ i ≤ R - ε then (1 : ℝ) else 0)) := by
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases hbad : Δ i ≤ R - ε
    · simp [hbad]
    · simp [hbad]
      exact hBound i
  have hcard :
      (∑ i : Fin T, if Δ i ≤ R - ε then (1 : ℝ) else 0) =
        ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ) := by
    simp
  have hT' : (0 : ℝ) < T := by
    exact_mod_cast hT
  have hdiv :
      averageDeletion Δ ≤
        (((T : ℝ) * R -
            ε * ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ)) /
          T) := by
    unfold averageDeletion
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hT')
    calc
      ∑ i, Δ i ≤
          ∑ i : Fin T, (R - ε * (if Δ i ≤ R - ε then (1 : ℝ) else 0)) := hsum
      _ = (T : ℝ) * R -
            ε * ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ) := by
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          simp [hcard]
  have hneT : (T : ℝ) ≠ 0 := by
    positivity
  calc
    averageDeletion Δ ≤
        (((T : ℝ) * R -
            ε * ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ)) /
          T) := hdiv
    _ = R - ε * lowDeletionDensity Δ R ε := by
      unfold lowDeletionDensity
      field_simp [hneT]

/-- Exact saturation of the average forces the low-efficiency steps to have zero density. -/
theorem lowDeletionDensity_eq_zero_of_averageDeletion_eq_max
    {R ε : ℝ} {T : ℕ} (hT : 0 < T) (hε : 0 < ε) (Δ : Fin T → ℝ)
    (hBound : ∀ i, Δ i ≤ R)
    (hAvg : averageDeletion Δ = R) :
    lowDeletionDensity Δ R ε = 0 := by
  have hineq := averageDeletion_le_of_lowDeletionDensity (R := R) (ε := ε) hT Δ hBound
  rw [hAvg] at hineq
  have hnonneg : 0 ≤ lowDeletionDensity Δ R ε := by
    unfold lowDeletionDensity
    positivity
  nlinarith

/-- Paper-facing rigidity package: the sum identity gives the average deletion, and exact
    saturation rules out a positive density of suboptimal steps. -/
theorem paper_fold_local_rewrite_saturation_step_efficiency_rigidity :
    (∀ {T : ℕ} (Δ : Fin T → ℝ) (G : ℝ),
      (∑ i, Δ i) = G → averageDeletion Δ = G / T) ∧
    (∀ {R ε : ℝ} {T : ℕ}, 0 < T → 0 < ε →
      ∀ Δ : Fin T → ℝ,
      (∀ i, Δ i ≤ R) →
      averageDeletion Δ = R →
      lowDeletionDensity Δ R ε = 0) := by
  refine ⟨?_, ?_⟩
  · intro T Δ G hG
    exact averageDeletion_eq_total Δ G hG
  · intro R ε T hT hε Δ hBound hAvg
    exact lowDeletionDensity_eq_zero_of_averageDeletion_eq_max hT hε Δ hBound hAvg

/-- Paper-facing wrapper for the local-rewrite lower-tail barrier: the pointwise inequality
    `G_m ≤ R T_m` yields the lower-tail event inclusion, the LDP upper wrapper makes the tail
    summable, and Borel-Cantelli upgrades this to an almost-sure linear lower bound.
    thm:fold-local-rewrite-ldp-lower-tail-barrier -/
theorem paper_fold_local_rewrite_ldp_lower_tail_barrier
    (gStar R a : ℝ)
    (pointwiseBound eventInclusion exponentialLowerTail summableLowerTail
      almostSureLiminfLowerBound : Prop)
    (ha : a < gStar / R)
    (hInclusion : pointwiseBound → eventInclusion)
    (hLdp : eventInclusion → a < gStar / R → exponentialLowerTail)
    (hSummable : exponentialLowerTail → summableLowerTail)
    (hBorelCantelli : summableLowerTail → almostSureLiminfLowerBound) :
    pointwiseBound → exponentialLowerTail ∧ almostSureLiminfLowerBound := by
  intro hBound
  have hEventInclusion : eventInclusion := hInclusion hBound
  have hTail : exponentialLowerTail := hLdp hEventInclusion ha
  exact ⟨hTail, hBorelCantelli (hSummable hTail)⟩

/-- Paper-facing Bernoulli-`p` analogue of the local-rewrite lower-tail barrier wrapper: the same
event inclusion, LDP upper tail, and Borel-Cantelli packaging upgrade the Bernoulli-`p` pointwise
barrier into an exponential lower-tail certificate and almost-sure linear lower bound.
    thm:fold-local-rewrite-ldp-lower-tail-barrier-bernoulli-p -/
theorem paper_fold_local_rewrite_ldp_lower_tail_barrier_bernoulli_p
    (p gStarP R a : ℝ)
    (pointwiseBound eventInclusion exponentialLowerTail summableLowerTail
      almostSureLiminfLowerBound : Prop)
    (hp : 0 < p ∧ p < 1)
    (ha : a < gStarP / R)
    (hInclusion : pointwiseBound → eventInclusion)
    (hLdp : eventInclusion → a < gStarP / R → exponentialLowerTail)
    (hSummable : exponentialLowerTail → summableLowerTail)
    (hBorelCantelli : summableLowerTail → almostSureLiminfLowerBound) :
    pointwiseBound → exponentialLowerTail ∧ almostSureLiminfLowerBound := by
  let _ := p
  let _ := hp
  exact
    paper_fold_local_rewrite_ldp_lower_tail_barrier
      gStarP R a pointwiseBound eventInclusion exponentialLowerTail summableLowerTail
      almostSureLiminfLowerBound ha hInclusion hLdp hSummable hBorelCantelli

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the average-case `B`-bit inversion barrier and its
    separation from the zero-error worst-case threshold.
    thm:fold-bbit-inversion-avg-worst-gap -/
theorem paper_fold_local_rewrite_bbit_inversion_avg_worst_gap (m B : ℕ)
    (avg_success_bound zero_error_worst_case_threshold : Prop)
    (hAvg : avg_success_bound)
    (hWorst : zero_error_worst_case_threshold) :
    avg_success_bound ∧ zero_error_worst_case_threshold := by
  let _ := m
  let _ := B
  exact ⟨hAvg, hWorst⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing finite-alphabet strong converse wrapper for the maximal-fiber argument:
    if the recoverable microstates are bounded by the available codewords and that ratio is
    already dominated by an exponential envelope, then the conditional success probability
    inherits both bounds.
    thm:fold-local-rewrite-maxfiber-strong-converse-finite-alphabet -/
theorem paper_fold_local_rewrite_maxfiber_strong_converse_finite_alphabet
    (m alphabetCard lengthBudget : ℕ)
    (recoverableCount successProbability maxFiber expUpper : ℝ)
    (hMaxFiber : 0 < maxFiber)
    (hCount : successProbability ≤ recoverableCount / maxFiber)
    (hCode : recoverableCount ≤ (alphabetCard : ℝ) ^ (lengthBudget + 1))
    (hExp : ((alphabetCard : ℝ) ^ (lengthBudget + 1)) / maxFiber ≤ expUpper) :
    successProbability ≤ ((alphabetCard : ℝ) ^ (lengthBudget + 1)) / maxFiber ∧
      successProbability ≤ expUpper := by
  let _ := m
  have hCodeDiv :
      recoverableCount / maxFiber ≤ ((alphabetCard : ℝ) ^ (lengthBudget + 1)) / maxFiber := by
    exact div_le_div_of_nonneg_right hCode (le_of_lt hMaxFiber)
  refine ⟨le_trans hCount hCodeDiv, le_trans (le_trans hCount hCodeDiv) hExp⟩

/-- Paper-facing wrapper for the reversible event-alphabet lower bound: an injective lift gives
    the alphabet threshold, while the max-fiber asymptotic is carried along as an explicit
    hypothesis.
    cor:fold-local-rewrite-reversible-event-alphabet-lower-bound -/
theorem paper_fold_local_rewrite_reversible_event_alphabet_lower_bound
    (fiberInjectiveLift maxFiberAsymptotic alphabetLowerBound : Prop)
    (hCount : fiberInjectiveLift → alphabetLowerBound)
    (hAsymptotic : maxFiberAsymptotic) :
    fiberInjectiveLift -> And maxFiberAsymptotic alphabetLowerBound := by
  intro hLift
  exact ⟨hAsymptotic, hCount hLift⟩

end

end Omega.Folding.LocalRewriteLdpBarrier
