universe u

namespace Omega.Zeta

/-- Paper label: `cor:xi-decidable-but-unrealizable-visible-query`. -/
theorem paper_xi_decidable_but_unrealizable_visible_query
    (Query : Type u) (readable finiteCertificate realizable : Query → Prop)
    (hCert : ∀ q, finiteCertificate q → readable q ∨ ¬ readable q)
    (hExists : ∃ q, finiteCertificate q ∧ ¬ realizable q) :
    ∃ q, (readable q ∨ ¬ readable q) ∧ ¬ realizable q :=
  match hExists with
  | ⟨q, hfinite, hunrealizable⟩ => ⟨q, hCert q hfinite, hunrealizable⟩

end Omega.Zeta
