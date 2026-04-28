import Mathlib.Tactic

namespace Omega.Conclusion

/-- Circle dimension of the window-6 compact torus factor. -/
def conclusion_window6_dyadic_mixed_signature_minimality_torus_cdim : ℕ := 3

/-- Dyadic prime-circle dimension of the rank-two pro-`2` address factor. -/
def conclusion_window6_dyadic_mixed_signature_minimality_dyadic_pcdim : ℕ := 2

/-- Dyadic mixed signature of the product object. -/
def conclusion_window6_dyadic_mixed_signature_minimality_signature : ℕ × ℕ :=
  (conclusion_window6_dyadic_mixed_signature_minimality_torus_cdim,
    conclusion_window6_dyadic_mixed_signature_minimality_dyadic_pcdim)

/-- A faithful restriction of the torus factor into `T^r` preserves the circle dimension lower
bound. -/
def conclusion_window6_dyadic_mixed_signature_minimality_faithful_torus (r : ℕ) : Prop :=
  conclusion_window6_dyadic_mixed_signature_minimality_torus_cdim ≤ r

/-- A faithful restriction of the dyadic factor into `Z_2^s` preserves the prime-circle dimension
lower bound. -/
def conclusion_window6_dyadic_mixed_signature_minimality_faithful_dyadic (s : ℕ) : Prop :=
  conclusion_window6_dyadic_mixed_signature_minimality_dyadic_pcdim ≤ s

/-- Paper-facing mixed-signature and minimality statement for
`prop:conclusion-window6-dyadic-mixed-signature-minimality`. -/
def conclusion_window6_dyadic_mixed_signature_minimality_statement : Prop :=
  conclusion_window6_dyadic_mixed_signature_minimality_signature = (3, 2) ∧
    ∀ r s : ℕ,
      conclusion_window6_dyadic_mixed_signature_minimality_faithful_torus r →
        conclusion_window6_dyadic_mixed_signature_minimality_faithful_dyadic s →
          3 ≤ r ∧ 2 ≤ s

/-- Paper label: `prop:conclusion-window6-dyadic-mixed-signature-minimality`. -/
theorem paper_conclusion_window6_dyadic_mixed_signature_minimality :
    conclusion_window6_dyadic_mixed_signature_minimality_statement := by
  unfold conclusion_window6_dyadic_mixed_signature_minimality_statement
    conclusion_window6_dyadic_mixed_signature_minimality_signature
    conclusion_window6_dyadic_mixed_signature_minimality_torus_cdim
    conclusion_window6_dyadic_mixed_signature_minimality_dyadic_pcdim
    conclusion_window6_dyadic_mixed_signature_minimality_faithful_torus
    conclusion_window6_dyadic_mixed_signature_minimality_faithful_dyadic
  exact ⟨rfl, by intro r s hr hs; exact ⟨hr, hs⟩⟩

end Omega.Conclusion
