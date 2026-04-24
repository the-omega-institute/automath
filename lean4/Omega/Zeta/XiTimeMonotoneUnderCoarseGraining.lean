import Mathlib

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-monotone-under-coarse-graining`.
If a finite-time protocol realizes `w` exactly via `t` alphabet-symbol emissions, then post-
composing the decoder with a coarse-graining map `C` realizes `C ∘ w` at the same time horizon.
The coarse output range is a quotient of the fine output range, and the resulting logarithmic gap
is bounded by the transcript budget `t * log |A|`. -/
theorem paper_xi_time_monotone_under_coarse_graining
    {Ω A W Wc : Type*} [Fintype Ω] [Fintype A] [Fintype W] [Fintype Wc]
    [DecidableEq Ω] [DecidableEq A] [DecidableEq W] [DecidableEq Wc]
    [Nonempty Ω] [Nonempty A]
    (w : Ω → W) (C : W → Wc) (t : ℕ)
    (hrealize :
      ∃ encoder : Ω → Fin t → A, ∃ decoder : (Fin t → A) → W,
        ∀ ω, decoder (encoder ω) = w ω) :
    (∃ encoder : Ω → Fin t → A, ∃ decoder : (Fin t → A) → Wc,
        ∀ ω, decoder (encoder ω) = C (w ω)) ∧
      Fintype.card (Set.range (C ∘ w)) ≤ Fintype.card (Set.range w) ∧
      Real.log (Fintype.card (Set.range w) : ℝ) -
          Real.log (Fintype.card (Set.range (C ∘ w)) : ℝ) ≤
        t * Real.log (Fintype.card A : ℝ) := by
  classical
  rcases hrealize with ⟨encoder, decoder, hdecoder⟩
  refine ⟨⟨encoder, C ∘ decoder, ?_⟩, ?_, ?_⟩
  · intro ω
    simp [Function.comp, hdecoder ω]
  · let paper_xi_time_monotone_under_coarse_graining_range_map :
        Set.range w → Set.range (C ∘ w) := fun y =>
          ⟨C y.1, by
            rcases y.2 with ⟨ω, hω⟩
            exact ⟨ω, by simp [Function.comp, hω]⟩⟩
    have hsurj : Function.Surjective
        paper_xi_time_monotone_under_coarse_graining_range_map := by
      intro z
      rcases z.2 with ⟨ω, hω⟩
      refine ⟨⟨w ω, ⟨ω, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      simpa [Function.comp] using hω
    exact Fintype.card_le_of_surjective
      paper_xi_time_monotone_under_coarse_graining_range_map hsurj
  · let paper_xi_time_monotone_under_coarse_graining_choose_transcript :
        Set.range w → (Fin t → A) := fun y =>
          encoder (Classical.choose y.2)
    have hchoose_inj : Function.Injective
        paper_xi_time_monotone_under_coarse_graining_choose_transcript := by
      intro y₁ y₂ hEq
      apply Subtype.ext
      calc
        y₁.1 = decoder
            (paper_xi_time_monotone_under_coarse_graining_choose_transcript y₁) := by
              simp [paper_xi_time_monotone_under_coarse_graining_choose_transcript, hdecoder,
                Classical.choose_spec y₁.2]
        _ = decoder
            (paper_xi_time_monotone_under_coarse_graining_choose_transcript y₂) := by
              simpa using congrArg decoder hEq
        _ = y₂.1 := by
              simp [paper_xi_time_monotone_under_coarse_graining_choose_transcript, hdecoder,
                Classical.choose_spec y₂.2]
    have hcard_range_w :
        Fintype.card (Set.range w) ≤ Fintype.card (Fin t → A) :=
      Fintype.card_le_of_injective
        paper_xi_time_monotone_under_coarse_graining_choose_transcript hchoose_inj
    have hcard_range_w' :
        Fintype.card (Set.range w) ≤ Fintype.card A ^ t := by
      simpa using hcard_range_w
    have hRangeW_nat : 0 < Fintype.card (Set.range w) := by
      refine Fintype.card_pos_iff.mpr ?_
      exact ⟨⟨w (Classical.choice ‹Nonempty Ω›), ⟨Classical.choice ‹Nonempty Ω›, rfl⟩⟩⟩
    have hRangeCW_nat : 0 < Fintype.card (Set.range (C ∘ w)) := by
      refine Fintype.card_pos_iff.mpr ?_
      exact ⟨⟨C (w (Classical.choice ‹Nonempty Ω›)),
        ⟨Classical.choice ‹Nonempty Ω›, rfl⟩⟩⟩
    have hRangeW_pos : 0 < (Fintype.card (Set.range w) : ℝ) := by
      exact_mod_cast hRangeW_nat
    have hcard_range_w_real :
        (Fintype.card (Set.range w) : ℝ) ≤ (Fintype.card A : ℝ) ^ t := by
      exact_mod_cast hcard_range_w'
    have hlog_range_w :
        Real.log (Fintype.card (Set.range w) : ℝ) ≤ t * Real.log (Fintype.card A : ℝ) := by
      have hlog_le :
          Real.log (Fintype.card (Set.range w) : ℝ) ≤
            Real.log ((Fintype.card A : ℝ) ^ t) := by
        exact Real.log_le_log hRangeW_pos hcard_range_w_real
      have hA_pos : 0 < (Fintype.card A : ℝ) := by positivity
      rw [← Real.rpow_natCast, Real.log_rpow hA_pos] at hlog_le
      simpa [Nat.cast_mul] using hlog_le
    have hlog_range_c_nonneg :
        0 ≤ Real.log (Fintype.card (Set.range (C ∘ w)) : ℝ) := by
      have hRangeCW_one : (1 : ℝ) ≤ Fintype.card (Set.range (C ∘ w)) := by
        exact_mod_cast Nat.succ_le_of_lt hRangeCW_nat
      exact Real.log_nonneg hRangeCW_one
    linarith

end Omega.Zeta
