import Omega.Conclusion.SectionLedgerKL

theorem paper_xi_fold_right_inverse_count_dispersion_lowerbound {X : Type*} [Fintype X]
    [Nonempty X] (d : X → ℕ) (N : ℕ) (Dsp : ℝ) (hN : 0 < N)
    (hd : ∀ x, 0 < d x)
    (hKL :
      Omega.Conclusion.SectionLedgerKL.klDivergence
          Omega.Conclusion.SectionLedgerKL.uniform
          (Omega.Conclusion.SectionLedgerKL.pushforward d N) ≤
        Real.log Dsp) :
    (Fintype.card X : ℝ) *
        (Real.log ((N : ℝ) / (Fintype.card X : ℝ)) - Real.log Dsp) ≤
      ∑ x, Real.log (d x : ℝ) := by
  rw [Omega.Conclusion.SectionLedgerKL.log_section_count_eq d N hN hd]
  have hcard_nonneg : 0 ≤ (Fintype.card X : ℝ) := by positivity
  nlinarith

