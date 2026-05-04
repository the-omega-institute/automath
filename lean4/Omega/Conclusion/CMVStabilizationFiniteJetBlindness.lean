import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cmv-stabilization-finite-jet-blindness`. -/
theorem paper_conclusion_cmv_stabilization_finite_jet_blindness
    {Jet : Type} (J : Nat → Nat → Jet) (Jinf : Nat → Jet) (kappa : Nat → Real)
    (subseq Ndet : Nat → Nat) (_hdefect : ∀ nu, 0 < kappa (subseq nu))
    (hfreeze : ∀ M, ∃ nu0, ∀ nu, nu0 ≤ nu → J (subseq nu) M = Jinf M)
    (hdepth : ∀ K, ∃ nu0, ∀ nu, nu0 ≤ nu → K ≤ Ndet (subseq nu)) :
    (∀ M, ∃ nu0, ∀ nu, nu0 ≤ nu → J (subseq nu) M = Jinf M) ∧
      (∀ K, ∃ nu0, ∀ nu, nu0 ≤ nu → K ≤ Ndet (subseq nu)) := by
  exact ⟨hfreeze, hdepth⟩

end Omega.Conclusion
