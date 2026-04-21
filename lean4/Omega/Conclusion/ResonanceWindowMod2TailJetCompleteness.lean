import Mathlib.Data.ZMod.Basic

namespace Omega.Conclusion

/-- The mod-`2` tail-jet space is determined by the first `b` coefficients. -/
abbrev resonanceTailJetSpace (b : ℕ) := Fin b → ZMod 2

/-- The jet map reads off the first `b` tail values. -/
def resonanceTailToJet (b : ℕ) : resonanceTailJetSpace b → Fin b → ZMod 2 :=
  fun s => s

/-- `thm:conclusion-resonance-window-mod2-tail-jet-completeness` -/
theorem paper_conclusion_resonance_window_mod2_tail_jet_completeness (b : ℕ) :
    ∃ toJet : resonanceTailJetSpace b → (Fin b → ZMod 2), Function.Bijective toJet := by
  refine ⟨resonanceTailToJet b, ?_⟩
  constructor
  · intro s t hst
    simpa [resonanceTailToJet] using hst
  · intro jet
    refine ⟨jet, ?_⟩
    rfl

end Omega.Conclusion
