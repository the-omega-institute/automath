namespace Omega.Zeta

universe u

/-- Paper label:
`thm:xi-time-part9k-fold-fiber-layer-count-realroot-logconcavity`. Uniformly combine the
real-negative-zero certificate with its Newton/log-concavity consequences on each fiber. -/
theorem paper_xi_time_part9k_fold_fiber_layer_count_realroot_logconcavity {Fiber : Type u}
    (RealNegativeZeros StrictLogConcave Unimodal : Fiber → Prop)
    (hzeros : ∀ x, RealNegativeZeros x)
    (hlog : ∀ x, RealNegativeZeros x → StrictLogConcave x ∧ Unimodal x) :
    ∀ x, RealNegativeZeros x ∧ StrictLogConcave x ∧ Unimodal x := by
  intro x
  have hz : RealNegativeZeros x := hzeros x
  rcases hlog x hz with ⟨hstrict, hunimodal⟩
  exact ⟨hz, hstrict, hunimodal⟩

end Omega.Zeta
