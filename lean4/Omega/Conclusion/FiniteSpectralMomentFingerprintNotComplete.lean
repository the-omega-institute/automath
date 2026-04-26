import Omega.SPG.UndecidableNoFiniteComputableCompleteInvariant

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-spectral-moment-fingerprint-not-complete`. -/
theorem paper_conclusion_finite_spectral_moment_fingerprint_not_complete {Obj : Type*}
    (equiv : Obj → Obj → Prop) (N : Nat) (Inv : Obj → Fin N)
    (hUndecidable : ¬ Omega.SPG.RelationDecidable equiv) :
    ¬ (∀ f g, equiv f g ↔ Inv f = Inv g) := by
  intro hComplete
  exact
    Omega.SPG.paper_spg_undecidable_no_finite_computable_complete_invariant equiv hUndecidable
      ⟨N, Inv, hComplete⟩

end Omega.Conclusion
