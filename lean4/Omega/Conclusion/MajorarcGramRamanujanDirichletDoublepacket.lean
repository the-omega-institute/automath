import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-majorarc-gram-ramanujan-dirichlet-doublepacket`. -/
theorem paper_conclusion_majorarc_gram_ramanujan_dirichlet_doublepacket
    (gramIdentity ramanujanPacketIdentity dirichletPacketIdentity : Prop) (hGram : gramIdentity)
    (hRam : gramIdentity → ramanujanPacketIdentity)
    (hDir : gramIdentity → dirichletPacketIdentity) :
    ramanujanPacketIdentity ∧ dirichletPacketIdentity := by
  exact ⟨hRam hGram, hDir hGram⟩

end Omega.Conclusion
